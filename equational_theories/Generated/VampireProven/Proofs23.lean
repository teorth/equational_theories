import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3349_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
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
  have eq515 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq348 eq10 -- superposition 10,348, 348 into 10, unify on (0).2 in 348 and (0).2 in 10
  subsumption eq515 eq486


@[equational_result]
theorem Equation1467_implies_Equation4068 (G : Type*) [Magma G] (h : Equation1467 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1467_implies_Equation1840 (G : Type*) [Magma G] (h : Equation1467 G) : Equation1840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq111 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq111 rfl


@[equational_result]
theorem Equation1467_implies_Equation3058 (G : Type*) [Magma G] (h : Equation1467 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1467_implies_Equation3331 (G : Type*) [Magma G] (h : Equation1467 G) : Equation3331 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq60 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq60 rfl


@[equational_result]
theorem Equation1467_implies_Equation3259 (G : Type*) [Magma G] (h : Equation1467 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq60 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq60 rfl


@[equational_result]
theorem Equation1467_implies_Equation1470 (G : Type*) [Magma G] (h : Equation1467 G) : Equation1470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.2 in 14
  have eq67 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq41 eq10 -- backward demodulation 10,41
  subsumption eq67 eq9


@[equational_result]
theorem Equation1467_implies_Equation3522 (G : Type*) [Magma G] (h : Equation1467 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 rfl


@[equational_result]
theorem Equation1467_implies_Equation4358 (G : Type*) [Magma G] (h : Equation1467 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.2 in 14
  have eq434 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq41 eq10 -- superposition 10,41, 41 into 10, unify on (0).2 in 41 and (0).2 in 10
  subsumption eq434 rfl


@[equational_result]
theorem Equation1467_implies_Equation4283 (G : Type*) [Magma G] (h : Equation1467 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.2 in 14
  have eq434 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq41 eq10 -- superposition 10,41, 41 into 10, unify on (0).2 in 41 and (0).2 in 10
  subsumption eq434 rfl


@[equational_result]
theorem Equation1467_implies_Equation2241 (G : Type*) [Magma G] (h : Equation1467 G) : Equation2241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2.2 in 14
  have eq65 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq40 eq11 -- backward demodulation 11,40
  have eq67 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq65 eq10 -- backward demodulation 10,65
  subsumption eq67 eq13


@[equational_result]
theorem Equation1467_implies_Equation2256 (G : Type*) [Magma G] (h : Equation1467 G) : Equation2256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq13


@[equational_result]
theorem Equation1467_implies_Equation2244 (G : Type*) [Magma G] (h : Equation1467 G) : Equation2244 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq13


@[equational_result]
theorem Equation1467_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1467 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.2 in 14
  have eq67 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := superpose eq41 eq10 -- backward demodulation 10,41
  subsumption eq67 eq13


@[equational_result]
theorem Equation1467_implies_Equation2279 (G : Type*) [Magma G] (h : Equation1467 G) : Equation2279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq13


@[equational_result]
theorem Equation259_implies_Equation2687 (G : Type*) [Magma G] (h : Equation259 G) : Equation2687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation259_implies_Equation3465 (G : Type*) [Magma G] (h : Equation259 G) : Equation3465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation259_implies_Equation3520 (G : Type*) [Magma G] (h : Equation259 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation259_implies_Equation3509 (G : Type*) [Magma G] (h : Equation259 G) : Equation3509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation259_implies_Equation3523 (G : Type*) [Magma G] (h : Equation259 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation259_implies_Equation2676 (G : Type*) [Magma G] (h : Equation259 G) : Equation2676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation259_implies_Equation2053 (G : Type*) [Magma G] (h : Equation259 G) : Equation2053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation259_implies_Equation2672 (G : Type*) [Magma G] (h : Equation259 G) : Equation2672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq12 eq13 -- forward demodulation 13,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation259_implies_Equation3264 (G : Type*) [Magma G] (h : Equation259 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3926_implies_Equation4135 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation3926_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq26 rfl


@[equational_result]
theorem Equation3926_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation4436 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq26 rfl


@[equational_result]
theorem Equation3926_implies_Equation3723 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation3730 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3730 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq22 eq17


@[equational_result]
theorem Equation3926_implies_Equation307 (G : Type*) [Magma G] (h : Equation3926 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq24 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq24 rfl


@[equational_result]
theorem Equation3926_implies_Equation4435 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation3727 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3727 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation3729 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation3926_implies_Equation3520 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation4672 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3926_implies_Equation4381 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation4130 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3926_implies_Equation377 (G : Type*) [Magma G] (h : Equation3926 G) : Equation377 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation4128 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3926_implies_Equation378 (G : Type*) [Magma G] (h : Equation3926 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3926_implies_Equation325 (G : Type*) [Magma G] (h : Equation3926 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3926_implies_Equation4134 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3926_implies_Equation4136 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4136 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq13


@[equational_result]
theorem Equation3926_implies_Equation4437 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation379 (G : Type*) [Magma G] (h : Equation3926 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation4141_implies_Equation3541 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4358 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4673 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK2) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq288 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (X0 ◇ X0)) := superpose eq286 eq28 -- backward demodulation 28,286
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq340 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X0 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq314 eq288 -- backward demodulation 288,314
  have eq388 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq340 eq340 -- superposition 340,340, 340 into 340, unify on (0).2 in 340 and (0).2 in 340
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : ((sK0 ◇ sK2) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq505 eq10 -- backward demodulation 10,505
  have eq561 : ((sK0 ◇ sK0) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq505 eq560 -- forward demodulation 560,505
  subsumption eq561 eq388


@[equational_result]
theorem Equation4141_implies_Equation3323 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3256 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3256 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq52 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq52 rfl


@[equational_result]
theorem Equation4141_implies_Equation4071 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq452 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq286 eq10 -- superposition 10,286, 286 into 10, unify on (0).2 in 286 and (0).2 in 10
  subsumption eq452 rfl


@[equational_result]
theorem Equation4141_implies_Equation3513 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq59 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).1.2 in 57
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq32 -- backward demodulation 32,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq59 -- superposition 59,325, 325 into 59, unify on (0).2 in 325 and (0).1 in 59
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation4672 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq288 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (X0 ◇ X0)) := superpose eq286 eq28 -- backward demodulation 28,286
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq340 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X0 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq314 eq288 -- backward demodulation 288,314
  have eq388 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq340 eq340 -- superposition 340,340, 340 into 340, unify on (0).2 in 340 and (0).2 in 340
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : ((sK0 ◇ sK0) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq388


@[equational_result]
theorem Equation4141_implies_Equation3324 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3324 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).2.1.1.1 in 17
  have eq78 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq123 eq13 -- backward demodulation 13,123
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq17 -- superposition 17,32, 32 into 17, unify on (0).2 in 32 and (0).2.1.1 in 17
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq122 eq32 -- superposition 32,122, 122 into 32, unify on (0).2 in 122 and (0).1.1.1 in 32
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq127 eq234 -- forward demodulation 234,127
  have eq262 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq261 eq63 -- backward demodulation 63,261
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq289 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq295 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq289 eq78 -- backward demodulation 78,289
  have eq310 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq265 eq295 -- forward demodulation 295,265
  have eq311 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq310 eq262 -- backward demodulation 262,310
  have eq312 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq311 eq20 -- backward demodulation 20,311
  have eq314 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq311 eq154 -- backward demodulation 154,311
  have eq340 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq311 eq312 -- forward demodulation 312,311
  have eq341 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq340 -- forward demodulation 340,9
  have eq342 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq341 eq314 -- forward demodulation 314,341
  have eq432 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq277 eq289 -- superposition 289,277, 277 into 289, unify on (0).2 in 277 and (0).1 in 289
  have eq459 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq432 eq10 -- backward demodulation 10,432
  subsumption eq459 eq342


@[equational_result]
theorem Equation4141_implies_Equation3306 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation4074 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).2.1.1.1 in 17
  have eq78 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq123 eq13 -- backward demodulation 13,123
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq17 -- superposition 17,32, 32 into 17, unify on (0).2 in 32 and (0).2.1.1 in 17
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq122 eq32 -- superposition 32,122, 122 into 32, unify on (0).2 in 122 and (0).1.1.1 in 32
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq127 eq234 -- forward demodulation 234,127
  have eq262 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq261 eq63 -- backward demodulation 63,261
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq289 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq295 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq289 eq78 -- backward demodulation 78,289
  have eq310 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq265 eq295 -- forward demodulation 295,265
  have eq311 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq310 eq262 -- backward demodulation 262,310
  have eq312 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq311 eq20 -- backward demodulation 20,311
  have eq314 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq311 eq154 -- backward demodulation 154,311
  have eq340 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq311 eq312 -- forward demodulation 312,311
  have eq341 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq340 -- forward demodulation 340,9
  have eq342 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq341 eq314 -- forward demodulation 314,341
  have eq432 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq277 eq289 -- superposition 289,277, 277 into 289, unify on (0).2 in 277 and (0).2 in 289
  have eq459 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq432 eq10 -- backward demodulation 10,432
  subsumption eq459 eq342


@[equational_result]
theorem Equation4141_implies_Equation4633 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq123 eq13 -- backward demodulation 13,123
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq222 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq12 eq122 -- superposition 122,12, 12 into 122, unify on (0).2 in 12 and (0).2 in 122
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq122 eq32 -- superposition 32,122, 122 into 32, unify on (0).2 in 122 and (0).1.1.1 in 32
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq127 eq234 -- forward demodulation 234,127
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq266 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X0) := superpose eq265 eq261 -- backward demodulation 261,265
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq289 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq432 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq277 eq289 -- superposition 289,277, 277 into 289, unify on (0).2 in 277 and (0).1 in 289
  have eq459 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq432 eq10 -- backward demodulation 10,432
  have eq460 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq266 eq459 -- forward demodulation 459,266
  subsumption eq460 eq222


@[equational_result]
theorem Equation4141_implies_Equation3260 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq20 eq19


@[equational_result]
theorem Equation4141_implies_Equation3315 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4121 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ X5) = (((((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X5) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2.1.1.1 in 18
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq205 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq122 -- superposition 122,18, 18 into 122, unify on (0).2 in 18 and (0).1.1 in 122
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq289 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = (((((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) ◇ X5) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq286 eq62 -- backward demodulation 62,286
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq300 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq286 eq205 -- backward demodulation 205,286
  have eq305 (X0 X2 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = (((X0 ◇ X2) ◇ X5) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq263 eq289 -- forward demodulation 289,263
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq309 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq263 eq300 -- forward demodulation 300,263
  have eq310 (X0 X4 X5 : G) : (X0 ◇ X5) = (((X0 ◇ X0) ◇ X4) ◇ X5) := superpose eq309 eq305 -- backward demodulation 305,309
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq347 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq346 eq10 -- backward demodulation 10,346
  have eq492 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq310 -- superposition 310,9, 9 into 310, unify on (0).2 in 9 and (0).2 in 310
  have eq686 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq492 eq347 -- superposition 347,492, 492 into 347, unify on (0).2 in 492 and (0).1 in 347
  subsumption eq686 rfl


@[equational_result]
theorem Equation4141_implies_Equation4286 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation4077 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq346


@[equational_result]
theorem Equation4141_implies_Equation3259 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3258 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation311 (G : Type*) [Magma G] (h : Equation4141 G) : Equation311 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3308 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation3534 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3326 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3321 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4073 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq20 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq20 eq29 -- forward demodulation 29,20
  have eq31 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq114 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq164 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq114 -- backward demodulation 114,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq164 -- forward demodulation 164,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq201 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq211 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq263 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq211 eq201 -- backward demodulation 201,211
  have eq274 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq263 eq182 -- backward demodulation 182,263
  have eq277 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq274 eq31 -- backward demodulation 31,274
  have eq297 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq274 eq277 -- forward demodulation 277,274
  have eq332 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) := superpose eq30 eq297 -- superposition 297,30, 30 into 297, unify on (0).2 in 30 and (0).2.1 in 297
  have eq360 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq274 eq332 -- forward demodulation 332,274
  have eq361 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq274 eq360 -- forward demodulation 360,274
  have eq466 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq20 eq361 -- superposition 361,20, 20 into 361, unify on (0).2 in 20 and (0).2 in 361
  have eq485 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq466 eq10 -- backward demodulation 10,466
  subsumption eq485 eq274


@[equational_result]
theorem Equation4141_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ X5) = (((((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X5) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2.1.1.1 in 18
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq205 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq122 -- superposition 122,18, 18 into 122, unify on (0).2 in 18 and (0).1.1 in 122
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq289 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = (((((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) ◇ X5) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq286 eq62 -- backward demodulation 62,286
  have eq300 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq286 eq205 -- backward demodulation 205,286
  have eq305 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq286 eq10 -- backward demodulation 10,286
  have eq306 (X0 X2 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = (((X0 ◇ X2) ◇ X5) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq263 eq289 -- forward demodulation 289,263
  have eq310 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq263 eq300 -- forward demodulation 300,263
  have eq311 (X0 X4 X5 : G) : (X0 ◇ X5) = (((X0 ◇ X0) ◇ X4) ◇ X5) := superpose eq310 eq306 -- backward demodulation 306,310
  have eq492 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq311 -- superposition 311,9, 9 into 311, unify on (0).2 in 9 and (0).2 in 311
  have eq686 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq492 eq305 -- superposition 305,492, 492 into 305, unify on (0).2 in 492 and (0).1 in 305
  subsumption eq686 rfl


@[equational_result]
theorem Equation4141_implies_Equation3469 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq289 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq432 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq277 eq289 -- superposition 289,277, 277 into 289, unify on (0).2 in 277 and (0).2 in 289
  have eq459 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := superpose eq432 eq10 -- backward demodulation 10,432
  subsumption eq459 eq432


@[equational_result]
theorem Equation4141_implies_Equation4603 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4603 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq123 eq13 -- backward demodulation 13,123
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq122 eq32 -- superposition 32,122, 122 into 32, unify on (0).2 in 122 and (0).1.1.1 in 32
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq127 eq234 -- forward demodulation 234,127
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq266 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X0) := superpose eq265 eq261 -- backward demodulation 261,265
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq288 : ((sK0 ◇ sK2) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq266 eq10 -- backward demodulation 10,266
  have eq290 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq423 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq290 eq277 -- superposition 277,290, 290 into 277, unify on (0).2 in 290 and (0).2 in 277
  have eq464 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq423 eq288 -- backward demodulation 288,423
  subsumption eq464 eq266


@[equational_result]
theorem Equation4141_implies_Equation4066 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq289 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq455 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq289 eq10 -- superposition 10,289, 289 into 10, unify on (0).2 in 289 and (0).2 in 10
  subsumption eq455 rfl


@[equational_result]
theorem Equation4141_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


@[equational_result]
theorem Equation4141_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq18 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq18 -- forward demodulation 18,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) := superpose eq12 eq102 -- forward demodulation 102,12
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq123 eq13 -- backward demodulation 13,123
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq17 eq32 -- superposition 32,17, 17 into 32, unify on (0).2 in 17 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq122 eq32 -- superposition 32,122, 122 into 32, unify on (0).2 in 122 and (0).1.1.1 in 32
  have eq238 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq261 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq127 eq234 -- forward demodulation 234,127
  have eq264 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq238 -- forward demodulation 238,11
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq264 -- forward demodulation 264,9
  have eq266 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X0) := superpose eq265 eq261 -- backward demodulation 261,265
  have eq268 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq265 eq193 -- backward demodulation 193,265
  have eq277 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq265 eq14 -- backward demodulation 14,265
  have eq289 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq265 eq268 -- forward demodulation 268,265
  have eq432 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq277 eq289 -- superposition 289,277, 277 into 289, unify on (0).2 in 277 and (0).1 in 289
  have eq459 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq432 eq10 -- backward demodulation 10,432
  subsumption eq459 eq266


@[equational_result]
theorem Equation4141_implies_Equation4675 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq505 eq10 -- backward demodulation 10,505
  have eq561 : ((sK0 ◇ sK0) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq505 eq560 -- forward demodulation 560,505
  subsumption eq561 rfl


@[equational_result]
theorem Equation4141_implies_Equation4360 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation3318 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq338 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- backward demodulation 20,325
  subsumption eq338 eq325


@[equational_result]
theorem Equation4141_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4072 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq452 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq286 eq10 -- superposition 10,286, 286 into 10, unify on (0).2 in 286 and (0).2 in 10
  subsumption eq452 rfl


@[equational_result]
theorem Equation4141_implies_Equation4153 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4153 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK3) ◇ sK4) := superpose eq505 eq10 -- backward demodulation 10,505
  have eq561 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq346 eq560 -- forward demodulation 560,346
  subsumption eq561 eq505


@[equational_result]
theorem Equation4141_implies_Equation3334 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq27 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq338 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- backward demodulation 20,325
  subsumption eq338 eq325


@[equational_result]
theorem Equation4141_implies_Equation4676 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq288 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ (X0 ◇ X0)) := superpose eq286 eq28 -- backward demodulation 28,286
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq340 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X0 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq314 eq288 -- backward demodulation 288,314
  have eq388 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq340 eq340 -- superposition 340,340, 340 into 340, unify on (0).2 in 340 and (0).2 in 340
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK0) ◇ sK4) := superpose eq505 eq10 -- backward demodulation 10,505
  have eq561 : ((sK0 ◇ sK0) ◇ sK4) ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq505 eq560 -- forward demodulation 560,505
  subsumption eq561 eq388


@[equational_result]
theorem Equation4141_implies_Equation3264 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation4079 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq346


@[equational_result]
theorem Equation4141_implies_Equation3463 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq621 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- superposition 10,505, 505 into 10, unify on (0).2 in 505 and (0).2 in 10
  subsumption eq621 rfl


@[equational_result]
theorem Equation4141_implies_Equation4134 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq346


@[equational_result]
theorem Equation4141_implies_Equation3253 (G : Type*) [Magma G] (h : Equation4141 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq16 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).2.1 in 8
  have eq18 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq8 eq16 -- forward demodulation 16,8
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq9 -- backward demodulation 9,18
  subsumption eq19 eq18


@[equational_result]
theorem Equation4141_implies_Equation329 (G : Type*) [Magma G] (h : Equation4141 G) : Equation329 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq51 -- forward demodulation 51,9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq57 -- forward demodulation 57,19
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.2 in 58
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq505 eq10 -- backward demodulation 10,505
  subsumption eq560 eq505


@[equational_result]
theorem Equation4141_implies_Equation323 (G : Type*) [Magma G] (h : Equation4141 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq24 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq29 -- forward demodulation 29,19
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.2 in 30
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq66 -- forward demodulation 66,12
  have eq95 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq118 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).2.1 in 12
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq83 -- superposition 83,11, 11 into 83, unify on (0).2 in 11 and (0).2 in 83
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq83 eq11 -- superposition 11,83, 83 into 11, unify on (0).2 in 83 and (0).2.1 in 11
  have eq177 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) := superpose eq149 eq118 -- backward demodulation 118,149
  have eq179 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq155 -- forward demodulation 155,11
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq179 -- forward demodulation 179,9
  have eq182 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq180 eq95 -- backward demodulation 95,180
  have eq184 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq180 eq47 -- backward demodulation 47,180
  have eq200 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4)) := superpose eq184 eq177 -- backward demodulation 177,184
  have eq210 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq184 -- superposition 184,9, 9 into 184, unify on (0).2 in 9 and (0).1 in 184
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq184 -- superposition 184,12, 12 into 184, unify on (0).2 in 12 and (0).2.1 in 184
  have eq261 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq210 eq200 -- backward demodulation 200,210
  have eq272 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq261 eq182 -- backward demodulation 182,261
  have eq305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq272 eq223 -- forward demodulation 223,272
  have eq325 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq305 -- superposition 305,19, 19 into 305, unify on (0).2 in 19 and (0).2 in 305
  have eq419 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq325 eq20 -- superposition 20,325, 325 into 20, unify on (0).2 in 325 and (0).1 in 20
  subsumption eq419 rfl


