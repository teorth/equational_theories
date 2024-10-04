import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3591_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3591 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X2) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq32 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.2 in 9
  have eq172 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq65 eq9 -- superposition 9,65, 65 into 9, unify on (0).2 in 65 and (0).2.2 in 9
  have eq257 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq32 -- superposition 32,11, 11 into 32, unify on (0).2 in 11 and (0).2 in 32
  have eq354 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq257 eq69 -- backward demodulation 69,257
  have eq406 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq65 eq257 -- superposition 257,65, 65 into 257, unify on (0).2 in 65 and (0).2.2.1 in 257
  have eq697 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ (X1 ◇ X3)) := superpose eq21 eq406 -- forward demodulation 406,21
  have eq907 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq172 eq10 -- superposition 10,172, 172 into 10, unify on (0).2 in 172 and (0).2 in 10
  have eq946 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq697 eq907 -- forward demodulation 907,697
  subsumption eq946 eq354


@[equational_result]
theorem Equation3591_implies_Equation3794 (G : Type*) [Magma G] (h : Equation3591 G) : Equation3794 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X2) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq32 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq69 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.2 in 9
  have eq172 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq65 eq9 -- superposition 9,65, 65 into 9, unify on (0).2 in 65 and (0).2.2 in 9
  have eq257 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq32 -- superposition 32,11, 11 into 32, unify on (0).2 in 11 and (0).2 in 32
  have eq354 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq257 eq69 -- backward demodulation 69,257
  have eq406 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq65 eq257 -- superposition 257,65, 65 into 257, unify on (0).2 in 65 and (0).2.2.1 in 257
  have eq697 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ (X1 ◇ X3)) := superpose eq21 eq406 -- forward demodulation 406,21
  have eq907 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK1)) := superpose eq172 eq10 -- superposition 10,172, 172 into 10, unify on (0).2 in 172 and (0).2 in 10
  have eq946 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq697 eq907 -- forward demodulation 907,697
  subsumption eq946 eq354


@[equational_result]
theorem Equation4209_implies_Equation359 (G : Type*) [Magma G] (h : Equation4209 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation4209_implies_Equation3962 (G : Type*) [Magma G] (h : Equation4209 G) : Equation3962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 eq12


@[equational_result]
theorem Equation4209_implies_Equation3862 (G : Type*) [Magma G] (h : Equation4209 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 eq11


@[equational_result]
theorem Equation4209_implies_Equation385 (G : Type*) [Magma G] (h : Equation4209 G) : Equation385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2737_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2737 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq28 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq34 : sK0 ≠ sK0 := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2 in 9
  subsumption eq34 rfl


@[equational_result]
theorem Equation1313_implies_Equation47 (G : Type*) [Magma G] (h : Equation1313 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq21 : sK0 ≠ sK0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation714_implies_Equation2847 (G : Type*) [Magma G] (h : Equation714 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2.1 in 10
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq10 eq14 -- forward demodulation 14,10
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq10 eq18 -- forward demodulation 18,10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).1.2 in 11
  have eq33 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := superpose eq24 eq9 -- backward demodulation 9,24
  have eq34 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq24 eq33 -- forward demodulation 33,24
  have eq42 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := superpose eq24 eq34 -- superposition 34,24, 24 into 34, unify on (0).2 in 24 and (0).2 in 34
  have eq45 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq24 eq42 -- forward demodulation 42,24
  have eq46 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq24 eq45 -- forward demodulation 45,24
  subsumption eq46 eq11


@[equational_result]
theorem Equation714_implies_Equation4435 (G : Type*) [Magma G] (h : Equation714 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq12 eq20 -- forward demodulation 20,12
  have eq25 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq21 eq12 -- superposition 12,21, 21 into 12, unify on (0).2 in 21 and (0).1.2 in 12
  have eq46 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq46 rfl


@[equational_result]
theorem Equation714_implies_Equation1223 (G : Type*) [Magma G] (h : Equation714 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2.1 in 10
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq10 eq14 -- forward demodulation 14,10
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq10 eq18 -- forward demodulation 18,10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq23 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0))) := superpose eq10 eq20 -- superposition 20,10, 10 into 20, unify on (0).2 in 10 and (0).2.2.2.1.1 in 20
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).1.2 in 11
  have eq27 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq23 -- forward demodulation 23,20
  have eq30 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := superpose eq27 eq9 -- backward demodulation 9,27
  have eq34 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq24 eq30 -- backward demodulation 30,24
  have eq35 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq24 eq34 -- forward demodulation 34,24
  subsumption eq35 eq11


@[equational_result]
theorem Equation714_implies_Equation3050 (G : Type*) [Magma G] (h : Equation714 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2.1 in 10
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq10 eq14 -- forward demodulation 14,10
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq10 eq18 -- forward demodulation 18,10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq19 -- forward demodulation 19,11
  have eq23 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0))) := superpose eq10 eq20 -- superposition 20,10, 10 into 20, unify on (0).2 in 10 and (0).2.2.2.1.1 in 20
  have eq24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).1.2 in 11
  have eq27 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq23 -- forward demodulation 23,20
  have eq30 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := superpose eq27 eq9 -- backward demodulation 9,27
  have eq34 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := superpose eq24 eq30 -- backward demodulation 30,24
  have eq35 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq24 eq34 -- forward demodulation 34,24
  have eq44 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := superpose eq24 eq35 -- superposition 35,24, 24 into 35, unify on (0).2 in 24 and (0).2 in 35
  have eq46 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq24 eq44 -- forward demodulation 44,24
  have eq47 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq24 eq46 -- forward demodulation 46,24
  subsumption eq47 eq11


@[equational_result]
theorem Equation714_implies_Equation2441 (G : Type*) [Magma G] (h : Equation714 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq12 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2.1 in 10
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq10 eq15 -- forward demodulation 15,10
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq10 eq19 -- forward demodulation 19,10
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq11 eq20 -- forward demodulation 20,11
  have eq36 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.2 in 11
  have eq67 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2 in 12
  have eq92 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq36 eq67 -- forward demodulation 67,36
  have eq93 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq36 eq92 -- forward demodulation 92,36
  subsumption eq93 eq11


@[equational_result]
theorem Equation168_implies_Equation3918 (G : Type*) [Magma G] (h : Equation168 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation168_implies_Equation3512 (G : Type*) [Magma G] (h : Equation168 G) : Equation3512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation168_implies_Equation3993 (G : Type*) [Magma G] (h : Equation168 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation168_implies_Equation3513 (G : Type*) [Magma G] (h : Equation168 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1484_implies_Equation3993 (G : Type*) [Magma G] (h : Equation1484 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation746_implies_Equation1695 (G : Type*) [Magma G] (h : Equation746 G) : Equation1695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq11 eq37 -- superposition 37,11, 11 into 37, unify on (0).2 in 11 and (0).1.1.1 in 37
  have eq227 : sK0 ≠ sK0 := superpose eq96 eq10 -- superposition 10,96, 96 into 10, unify on (0).2 in 96 and (0).2 in 10
  subsumption eq227 rfl


@[equational_result]
theorem Equation746_implies_Equation1848 (G : Type*) [Magma G] (h : Equation746 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq76 (X0 : G) : sK0 ≠ ((X0 ◇ (sK1 ◇ X0)) ◇ (sK0 ◇ sK1)) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.1 in 10
  have eq130 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := superpose eq35 eq76 -- superposition 76,35, 35 into 76, unify on (0).2 in 35 and (0).2 in 76
  subsumption eq130 eq9


@[equational_result]
theorem Equation746_implies_Equation4332 (G : Type*) [Magma G] (h : Equation746 G) : Equation4332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK2 ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq76 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq76 eq33


@[equational_result]
theorem Equation746_implies_Equation2902 (G : Type*) [Magma G] (h : Equation746 G) : Equation2902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq11 eq33 -- superposition 33,11, 11 into 33, unify on (0).2 in 11 and (0).1 in 33
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).1.1.1 in 35
  have eq230 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq96 eq35 -- superposition 35,96, 96 into 35, unify on (0).2 in 96 and (0).1.1 in 35
  have eq233 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X1 := superpose eq96 eq49 -- superposition 49,96, 96 into 49, unify on (0).2 in 96 and (0).1.2 in 49
  have eq875 (X0 : G) : sK0 ≠ (((X0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) := superpose eq230 eq10 -- superposition 10,230, 230 into 10, unify on (0).2 in 230 and (0).2.1 in 10
  subsumption eq875 eq233


@[equational_result]
theorem Equation2056_implies_Equation3258 (G : Type*) [Magma G] (h : Equation2056 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2045_implies_Equation4314 (G : Type*) [Magma G] (h : Equation2045 G) : Equation4314 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.1 in 13
  have eq442 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3) = (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.1 in 20
  have eq553 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := superpose eq13 eq442 -- forward demodulation 442,13
  have eq779 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).2.1 in 20
  have eq792 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq814 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq779 eq792 -- forward demodulation 792,779
  have eq1236 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) ◇ X4)) := superpose eq20 eq814 -- superposition 814,20, 20 into 814, unify on (0).2 in 20 and (0).2.2.1.1 in 814
  have eq1363 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X4)) := superpose eq553 eq1236 -- forward demodulation 1236,553
  have eq1616 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X2)) := superpose eq1363 eq1363 -- superposition 1363,1363, 1363 into 1363, unify on (0).2 in 1363 and (0).1 in 1363
  have eq1758 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq1363 eq10 -- superposition 10,1363, 1363 into 10, unify on (0).2 in 1363 and (0).2 in 10
  subsumption eq1758 eq1616


@[equational_result]
theorem Equation2045_implies_Equation4282 (G : Type*) [Magma G] (h : Equation2045 G) : Equation4282 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.1 in 13
  have eq442 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3) = (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.1 in 20
  have eq553 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := superpose eq13 eq442 -- forward demodulation 442,13
  have eq779 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).2.1 in 20
  have eq792 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq814 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq779 eq792 -- forward demodulation 792,779
  have eq1236 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) ◇ X4)) := superpose eq20 eq814 -- superposition 814,20, 20 into 814, unify on (0).2 in 20 and (0).2.2.1.1 in 814
  have eq1363 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X4)) := superpose eq553 eq1236 -- forward demodulation 1236,553
  have eq1364 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq1363 eq10 -- backward demodulation 10,1363
  subsumption eq1364 eq1363


@[equational_result]
theorem Equation2045_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2045 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.1 in 13
  have eq442 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3) = (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).1.1 in 20
  have eq553 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := superpose eq13 eq442 -- forward demodulation 442,13
  have eq779 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq21 eq20 -- superposition 20,21, 21 into 20, unify on (0).2 in 21 and (0).2.1 in 20
  have eq792 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq814 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq779 eq792 -- forward demodulation 792,779
  have eq1236 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) ◇ X4)) := superpose eq20 eq814 -- superposition 814,20, 20 into 814, unify on (0).2 in 20 and (0).2.2.1.1 in 814
  have eq1363 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X4)) := superpose eq553 eq1236 -- forward demodulation 1236,553
  have eq1364 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq1363 eq10 -- backward demodulation 10,1363
  subsumption eq1364 eq1363


@[equational_result]
theorem Equation2550_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2550 G) : Equation2804 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1518_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1518 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation1518_implies_Equation359 (G : Type*) [Magma G] (h : Equation1518 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation2663_implies_Equation4656 (G : Type*) [Magma G] (h : Equation2663 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq15 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq14 -- forward demodulation 14,11
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq49 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq49 eq43


@[equational_result]
theorem Equation2663_implies_Equation307 (G : Type*) [Magma G] (h : Equation2663 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq10 eq8 -- backward demodulation 8,10
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation4448_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq151 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK1) ◇ sK0) := superpose eq17 eq37 -- superposition 37,17, 17 into 37, unify on (0).2 in 17 and (0).2 in 37
  subsumption eq151 eq68


@[equational_result]
theorem Equation4448_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK2 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq511 (X0 : G) : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq511 eq271


@[equational_result]
theorem Equation4448_implies_Equation4693 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK3 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK3 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq511 (X0 : G) : (sK2 ◇ (sK0 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq511 eq271


@[equational_result]
theorem Equation4448_implies_Equation4606 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq482 (X0 : G) : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq482 eq271


@[equational_result]
theorem Equation4448_implies_Equation4619 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK2 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq511 (X0 : G) : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq511 eq271


@[equational_result]
theorem Equation4448_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq270 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq510 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq270 eq11 -- superposition 11,270, 270 into 11, unify on (0).2 in 270 and (0).1 in 11
  subsumption eq510 eq270


@[equational_result]
theorem Equation4448_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK1 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK0 ◇ sK2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq511 (X0 : G) : (sK2 ◇ (sK0 ◇ sK2)) ≠ (sK2 ◇ (X0 ◇ sK2)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq511 eq271


@[equational_result]
theorem Equation4448_implies_Equation4611 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq482 (X0 : G) : (sK1 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq482 eq271


@[equational_result]
theorem Equation4448_implies_Equation4642 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq64 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq16 -- superposition 16,15, 15 into 16, unify on (0).2 in 15 and (0).2 in 16
  have eq271 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq64 eq64 -- superposition 64,64, 64 into 64, unify on (0).2 in 64 and (0).2 in 64
  have eq511 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq271 eq12 -- superposition 12,271, 271 into 12, unify on (0).2 in 271 and (0).1 in 12
  subsumption eq511 eq271


@[equational_result]
theorem Equation4448_implies_Equation4388 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK1) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq270 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq510 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq270 eq11 -- superposition 11,270, 270 into 11, unify on (0).2 in 270 and (0).1 in 11
  subsumption eq510 eq270


@[equational_result]
theorem Equation4448_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4452 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq37 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq151 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq37 -- superposition 37,17, 17 into 37, unify on (0).2 in 17 and (0).2 in 37
  subsumption eq151 eq68


@[equational_result]
theorem Equation4448_implies_Equation4438 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2 in 15
  have eq270 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X3)) = (X3 ◇ (X5 ◇ X3)) := superpose eq63 eq63 -- superposition 63,63, 63 into 63, unify on (0).2 in 63 and (0).2 in 63
  have eq510 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose eq270 eq11 -- superposition 11,270, 270 into 11, unify on (0).2 in 270 and (0).1 in 11
  subsumption eq510 eq270


@[equational_result]
theorem Equation4448_implies_Equation4456 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK1) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation4448_implies_Equation4464 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X0 ◇ X4) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq33 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ X0) ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  have eq138 (X1 X2 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (((X1 ◇ X2) ◇ sK2) ◇ sK0) := superpose eq17 eq33 -- superposition 33,17, 17 into 33, unify on (0).2 in 17 and (0).2 in 33
  subsumption eq138 eq68


@[equational_result]
theorem Equation827_implies_Equation413 (G : Type*) [Magma G] (h : Equation827 G) : Equation413 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq89 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation827_implies_Equation414 (G : Type*) [Magma G] (h : Equation827 G) : Equation414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq60 : sK0 ≠ sK0 := superpose eq22 eq18 -- superposition 18,22, 22 into 18, unify on (0).2 in 22 and (0).2 in 18
  subsumption eq60 rfl


@[equational_result]
theorem Equation827_implies_Equation412 (G : Type*) [Magma G] (h : Equation827 G) : Equation412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq44 : sK0 ≠ (sK0 ◇ sK0) := superpose eq39 eq10 -- backward demodulation 10,39
  subsumption eq44 eq17


@[equational_result]
theorem Equation827_implies_Equation415 (G : Type*) [Magma G] (h : Equation827 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq89 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq89 rfl


@[equational_result]
theorem Equation827_implies_Equation102 (G : Type*) [Magma G] (h : Equation827 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1432_implies_Equation3050 (G : Type*) [Magma G] (h : Equation1432 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation1432_implies_Equation3522 (G : Type*) [Magma G] (h : Equation1432 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1432_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1432 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation1432_implies_Equation4118 (G : Type*) [Magma G] (h : Equation1432 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1432_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1432 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation1432_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1432 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation1432_implies_Equation23 (G : Type*) [Magma G] (h : Equation1432 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation3738_implies_Equation4519 (G : Type*) [Magma G] (h : Equation3738 G) : Equation4519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X4) = ((X0 ◇ X2) ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = ((X4 ◇ X5) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq36 rfl


@[equational_result]
theorem Equation3738_implies_Equation4398 (G : Type*) [Magma G] (h : Equation3738 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X4) = ((X0 ◇ X2) ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = ((X4 ◇ X5) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq36 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq36 rfl


@[equational_result]
theorem Equation2046_implies_Equation2056 (G : Type*) [Magma G] (h : Equation2046 G) : Equation2056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq25 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK2 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq9


@[equational_result]
theorem Equation2046_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2046 G) : Equation2050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq25 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq9


@[equational_result]
theorem Equation2046_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2046 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation2046_implies_Equation4631 (G : Type*) [Magma G] (h : Equation2046 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq25 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq20


@[equational_result]
theorem Equation2046_implies_Equation3306 (G : Type*) [Magma G] (h : Equation2046 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2.1 in 13
  have eq238 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq9 eq31 -- superposition 31,9, 9 into 31, unify on (0).2 in 9 and (0).2.1.1 in 31
  have eq373 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq238 -- superposition 238,11, 11 into 238, unify on (0).2 in 11 and (0).2.1 in 238
  have eq407 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq373 -- forward demodulation 373,9
  have eq903 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq407 eq9 -- superposition 9,407, 407 into 9, unify on (0).2 in 407 and (0).1.1 in 9
  have eq1053 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq903 eq10 -- superposition 10,903, 903 into 10, unify on (0).2 in 903 and (0).2 in 10
  subsumption eq1053 rfl


@[equational_result]
theorem Equation2046_implies_Equation3316 (G : Type*) [Magma G] (h : Equation2046 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2.1 in 13
  have eq238 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq9 eq31 -- superposition 31,9, 9 into 31, unify on (0).2 in 9 and (0).2.1.1 in 31
  have eq373 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq238 -- superposition 238,11, 11 into 238, unify on (0).2 in 11 and (0).2.1 in 238
  have eq407 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq373 -- forward demodulation 373,9
  have eq903 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq407 eq9 -- superposition 9,407, 407 into 9, unify on (0).2 in 407 and (0).1.1 in 9
  have eq1087 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq903 eq10 -- superposition 10,903, 903 into 10, unify on (0).2 in 903 and (0).2 in 10
  subsumption eq1087 rfl


@[equational_result]
theorem Equation2046_implies_Equation3326 (G : Type*) [Magma G] (h : Equation2046 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2.1 in 13
  have eq238 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq9 eq31 -- superposition 31,9, 9 into 31, unify on (0).2 in 9 and (0).2.1.1 in 31
  have eq373 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq238 -- superposition 238,11, 11 into 238, unify on (0).2 in 11 and (0).2.1 in 238
  have eq407 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq373 -- forward demodulation 373,9
  have eq903 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq407 eq9 -- superposition 9,407, 407 into 9, unify on (0).2 in 407 and (0).1.1 in 9
  have eq1087 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq903 eq10 -- superposition 10,903, 903 into 10, unify on (0).2 in 903 and (0).2 in 10
  subsumption eq1087 rfl


@[equational_result]
theorem Equation3495_implies_Equation307 (G : Type*) [Magma G] (h : Equation3495 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2.1 in 8
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq415 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq12 eq115 -- superposition 115,12, 12 into 115, unify on (0).2 in 12 and (0).2.2 in 115
  have eq504 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq415 eq9 -- superposition 9,415, 415 into 9, unify on (0).2 in 415 and (0).2 in 9
  subsumption eq504 rfl


@[equational_result]
theorem Equation3495_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3495 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X3 ◇ (X2 ◇ (X3 ◇ X3))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.2 in 14
  have eq214 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq257 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).1.1.1 in 15
  have eq310 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq15 eq257 -- forward demodulation 257,15
  have eq315 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq416 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.2 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq696 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq461 eq10 -- superposition 10,461, 461 into 10, unify on (0).2 in 461 and (0).2 in 10
  subsumption eq696 rfl


@[equational_result]
theorem Equation3495_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3495 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X3 ◇ ((X4 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X3 ◇ (X2 ◇ (X3 ◇ X3))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.2 in 14
  have eq212 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq11 eq165 -- superposition 165,11, 11 into 165, unify on (0).2 in 11 and (0).2 in 165
  have eq214 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq257 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).1.1.1 in 15
  have eq310 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq15 eq257 -- forward demodulation 257,15
  have eq315 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq352 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq310 eq11 -- superposition 11,310, 310 into 11, unify on (0).2 in 310 and (0).2.2 in 11
  have eq416 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.2 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq469 (X0 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq461 eq212 -- backward demodulation 212,461
  have eq473 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq469 eq352 -- backward demodulation 352,469
  have eq922 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq473 eq10 -- superposition 10,473, 473 into 10, unify on (0).2 in 473 and (0).2 in 10
  subsumption eq922 rfl


@[equational_result]
theorem Equation852_implies_Equation4065 (G : Type*) [Magma G] (h : Equation852 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq16 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq9 -- backward demodulation 9,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation852_implies_Equation47 (G : Type*) [Magma G] (h : Equation852 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation852_implies_Equation52 (G : Type*) [Magma G] (h : Equation852 G) : Equation52 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation837_implies_Equation107 (G : Type*) [Magma G] (h : Equation837 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X3)) = ((X0 ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq72 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1 in 14
  have eq73 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq251 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq73 eq17 -- superposition 17,73, 73 into 17, unify on (0).2 in 73 and (0).2.2 in 17
  have eq712 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq72 eq251 -- superposition 251,72, 72 into 251, unify on (0).2 in 72 and (0).2.2 in 251
  have eq3261 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq712 eq9 -- superposition 9,712, 712 into 9, unify on (0).2 in 712 and (0).1.2 in 9
  have eq3617 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq3261 eq9 -- superposition 9,3261, 3261 into 9, unify on (0).2 in 3261 and (0).1.2 in 9
  have eq4043 : sK0 ≠ sK0 := superpose eq3617 eq10 -- superposition 10,3617, 3617 into 10, unify on (0).2 in 3617 and (0).2 in 10
  subsumption eq4043 rfl


@[equational_result]
theorem Equation837_implies_Equation105 (G : Type*) [Magma G] (h : Equation837 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1353_implies_Equation151 (G : Type*) [Magma G] (h : Equation1353 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X3 ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq16 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq48 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq48 rfl


@[equational_result]
theorem Equation1353_implies_Equation159 (G : Type*) [Magma G] (h : Equation1353 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X3 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq49 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation2082_implies_Equation4599 (G : Type*) [Magma G] (h : Equation2082 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq62 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq62 eq22


@[equational_result]
theorem Equation2082_implies_Equation4631 (G : Type*) [Magma G] (h : Equation2082 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq56 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ X0) ◇ sK0) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq56 eq22


@[equational_result]
theorem Equation2082_implies_Equation4675 (G : Type*) [Magma G] (h : Equation2082 G) : Equation4675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq13 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq56 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ sK2) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq56 eq22


@[equational_result]
theorem Equation3477_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3477 G) : Equation3499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq39 rfl


@[equational_result]
theorem Equation2856_implies_Equation255 (G : Type*) [Magma G] (h : Equation2856 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.1 in 10
  have eq16 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq21 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation4103_implies_Equation4086 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4112 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4116 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4116 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4111 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation1469_implies_Equation4131 (G : Type*) [Magma G] (h : Equation1469 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq208 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X0) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.2 in 9
  have eq296 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq208 eq10 -- superposition 10,208, 208 into 10, unify on (0).2 in 208 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation1469_implies_Equation4128 (G : Type*) [Magma G] (h : Equation1469 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq209 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X0) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.2 in 9
  have eq279 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq209 eq10 -- superposition 10,209, 209 into 10, unify on (0).2 in 209 and (0).2 in 10
  subsumption eq279 rfl


@[equational_result]
theorem Equation1469_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1469 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq209 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X0) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.2 in 9
  have eq279 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq209 eq10 -- superposition 10,209, 209 into 10, unify on (0).2 in 209 and (0).2 in 10
  subsumption eq279 rfl


@[equational_result]
theorem Equation1469_implies_Equation4134 (G : Type*) [Magma G] (h : Equation1469 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq209 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X0) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.2 in 9
  have eq279 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq209 eq10 -- superposition 10,209, 209 into 10, unify on (0).2 in 209 and (0).2 in 10
  subsumption eq279 rfl


@[equational_result]
theorem Equation427_implies_Equation1020 (G : Type*) [Magma G] (h : Equation427 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation4614_implies_Equation4656 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq34 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq73 (X0 X1 : G) : ((X0 ◇ sK1) ◇ sK1) ≠ ((X1 ◇ sK2) ◇ sK2) := superpose eq12 eq34 -- superposition 34,12, 12 into 34, unify on (0).2 in 12 and (0).1 in 34
  have eq146 (X0 X1 : G) : ((X1 ◇ sK2) ◇ sK2) ≠ ((sK1 ◇ sK1) ◇ X0) := superpose eq17 eq73 -- superposition 73,17, 17 into 73, unify on (0).2 in 17 and (0).1 in 73
  have eq287 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq342 (X1 X2 : G) : ((sK1 ◇ sK1) ◇ X2) ≠ ((X1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := superpose eq11 eq146 -- superposition 146,11, 11 into 146, unify on (0).2 in 11 and (0).1 in 146
  subsumption eq342 eq287


@[equational_result]
theorem Equation4614_implies_Equation4627 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4627 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK3) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq34 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK3) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq73 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ X0) ≠ ((X1 ◇ sK3) ◇ sK3) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq305 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq341 (X1 X2 : G) : ((sK0 ◇ sK0) ◇ X2) ≠ ((X1 ◇ (sK3 ◇ sK3)) ◇ (sK3 ◇ sK3)) := superpose eq11 eq73 -- superposition 73,11, 11 into 73, unify on (0).2 in 11 and (0).2 in 73
  subsumption eq341 eq305


@[equational_result]
theorem Equation4614_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq289 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq316 (X1 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := superpose eq11 eq18 -- superposition 18,11, 11 into 18, unify on (0).2 in 11 and (0).2 in 18
  subsumption eq316 eq289


@[equational_result]
theorem Equation4614_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq34 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq73 (X0 X1 : G) : ((sK0 ◇ sK0) ◇ X0) ≠ ((X1 ◇ sK1) ◇ sK1) := superpose eq17 eq34 -- superposition 34,17, 17 into 34, unify on (0).2 in 17 and (0).1 in 34
  have eq305 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq341 (X1 X2 : G) : ((sK0 ◇ sK0) ◇ X2) ≠ ((X1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := superpose eq11 eq73 -- superposition 73,11, 11 into 73, unify on (0).2 in 11 and (0).2 in 73
  subsumption eq341 eq305


@[equational_result]
theorem Equation4614_implies_Equation4591 (G : Type*) [Magma G] (h : Equation4614 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq18 (X0 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ sK0) ◇ sK0) ≠ ((X1 ◇ sK1) ◇ sK1) := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq119 (X0 X1 : G) : ((sK1 ◇ sK1) ◇ X0) ≠ ((X1 ◇ sK0) ◇ sK0) := superpose eq17 eq20 -- superposition 20,17, 17 into 20, unify on (0).2 in 17 and (0).2 in 20
  have eq342 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  have eq375 (X1 X2 : G) : ((sK1 ◇ sK1) ◇ X2) ≠ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := superpose eq11 eq119 -- superposition 119,11, 11 into 119, unify on (0).2 in 11 and (0).2 in 119
  subsumption eq375 eq342


@[equational_result]
theorem Equation3492_implies_Equation3496 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq40 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK1) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK1)) ◇ X1)) ◇ (sK1 ◇ sK1)) := superpose eq14 eq40 -- superposition 40,14, 14 into 40, unify on (0).2 in 14 and (0).2.2 in 40
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK1 ◇ sK1)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


@[equational_result]
theorem Equation3492_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3504 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq43 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK3) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK3)) ◇ X1)) ◇ (sK3 ◇ sK3)) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).2.2 in 43
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ X1) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK3 ◇ sK3)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


@[equational_result]
theorem Equation3492_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq62 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq92 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq99 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = (X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq100 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  have eq116 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq100 eq62 -- backward demodulation 62,100
  have eq184 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq16 eq92 -- superposition 92,16, 16 into 92, unify on (0).2 in 16 and (0).2 in 92
  have eq199 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X3 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3))) := superpose eq92 eq14 -- superposition 14,92, 92 into 14, unify on (0).2 in 92 and (0).2.2.2.1 in 14
  have eq227 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq9 eq199 -- forward demodulation 199,9
  have eq228 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq116 eq227 -- forward demodulation 227,116
  have eq247 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X3 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X3)) := superpose eq92 eq12 -- superposition 12,92, 92 into 12, unify on (0).2 in 92 and (0).1.2 in 12
  have eq290 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq99 eq247 -- forward demodulation 247,99
  have eq291 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq228 eq290 -- forward demodulation 290,228
  have eq411 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq184 eq10 -- superposition 10,184, 184 into 10, unify on (0).2 in 184 and (0).1 in 10
  subsumption eq411 eq291


@[equational_result]
theorem Equation3492_implies_Equation3500 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq43 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK2) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK2)) ◇ X1)) ◇ (sK2 ◇ sK2)) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).2.2 in 43
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK2 ◇ sK2)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


@[equational_result]
theorem Equation3492_implies_Equation4341 (G : Type*) [Magma G] (h : Equation3492 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq92 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq184 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq16 eq92 -- superposition 92,16, 16 into 92, unify on (0).2 in 16 and (0).2 in 92
  have eq411 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq184 eq10 -- superposition 10,184, 184 into 10, unify on (0).2 in 184 and (0).2.2 in 10
  subsumption eq411 rfl


@[equational_result]
theorem Equation3492_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq92 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.1 in 16
  have eq100 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  have eq184 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq16 eq92 -- superposition 92,16, 16 into 92, unify on (0).2 in 16 and (0).2 in 92
  have eq411 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq184 eq10 -- superposition 10,184, 184 into 10, unify on (0).2 in 184 and (0).1 in 10
  subsumption eq411 eq100


@[equational_result]
theorem Equation3492_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq43 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK1) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK1)) ◇ X1)) ◇ (sK1 ◇ sK1)) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).2.2 in 43
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK1 ◇ sK1)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


@[equational_result]
theorem Equation3492_implies_Equation3464 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq43 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ ((X1 ◇ sK1) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq111 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.1 in 15
  have eq128 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq111 eq72 -- backward demodulation 72,111
  have eq133 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq11 eq14 -- superposition 14,11, 11 into 14, unify on (0).2 in 11 and (0).2.1 in 14
  have eq159 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ ((X2 ◇ (X0 ◇ sK1)) ◇ X1)) ◇ (sK1 ◇ sK1)) := superpose eq14 eq43 -- superposition 43,14, 14 into 43, unify on (0).2 in 14 and (0).2.2 in 43
  have eq170 (X2 X3 X4 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) ◇ X5))) := superpose eq17 eq133 -- forward demodulation 133,17
  have eq286 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq339 (X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq128 eq286 -- forward demodulation 286,128
  have eq357 (X2 X3 X5 X6 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ ((X6 ◇ (X3 ◇ X3)) ◇ X5))) := superpose eq339 eq170 -- backward demodulation 170,339
  have eq373 (X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (sK1 ◇ sK1)) := superpose eq339 eq159 -- backward demodulation 159,339
  have eq378 (X2 X3 X5 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X5 ◇ X5)) := superpose eq339 eq357 -- forward demodulation 357,339
  subsumption eq373 eq378


@[equational_result]
theorem Equation621_implies_Equation616 (G : Type*) [Magma G] (h : Equation621 G) : Equation616 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation621_implies_Equation622 (G : Type*) [Magma G] (h : Equation621 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation621_implies_Equation625 (G : Type*) [Magma G] (h : Equation621 G) : Equation625 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation4485_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK2 ◇ (sK0 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4619 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK2 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4475 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq67 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2 in 16
  have eq299 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq67 eq67 -- superposition 67,67, 67 into 67, unify on (0).2 in 67 and (0).2 in 67
  have eq596 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq299 eq11 -- superposition 11,299, 299 into 11, unify on (0).2 in 299 and (0).1 in 11
  subsumption eq596 eq299


@[equational_result]
theorem Equation4485_implies_Equation4666 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK2 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq575 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq575 eq307


@[equational_result]
theorem Equation4485_implies_Equation4611 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4611 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq562 (X0 : G) : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq562 eq300


@[equational_result]
theorem Equation4485_implies_Equation4388 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4388 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq606 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq606 eq307


@[equational_result]
theorem Equation4485_implies_Equation4642 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK0 ◇ (sK2 ◇ sK2)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4497 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq606 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq606 eq307


@[equational_result]
theorem Equation4485_implies_Equation4489 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq575 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq575 eq307


@[equational_result]
theorem Equation4485_implies_Equation4689 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK3 ◇ sK3)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK3 ◇ sK3)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK2 ◇ (sK0 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4693 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK4) ◇ sK2) := mod_symm nh
  have eq11 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK3 ◇ sK3)) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 : (sK2 ◇ (sK3 ◇ sK3)) ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq15 eq17 -- superposition 17,15, 15 into 17, unify on (0).2 in 15 and (0).2 in 17
  have eq300 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq68 eq68 -- superposition 68,68, 68 into 68, unify on (0).2 in 68 and (0).2 in 68
  have eq597 (X0 : G) : (sK2 ◇ (sK0 ◇ sK0)) ≠ (sK2 ◇ (X0 ◇ X0)) := superpose eq300 eq12 -- superposition 12,300, 300 into 12, unify on (0).2 in 300 and (0).1 in 12
  subsumption eq597 eq300


@[equational_result]
theorem Equation4485_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4391 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : ((sK1 ◇ sK2) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq606 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq606 eq307


@[equational_result]
theorem Equation4485_implies_Equation4501 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ X4) ◇ X3) := superpose eq13 eq15 -- superposition 15,13, 13 into 15, unify on (0).2 in 13 and (0).2 in 15
  have eq307 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X5 ◇ X5)) := superpose eq73 eq73 -- superposition 73,73, 73 into 73, unify on (0).2 in 73 and (0).2 in 73
  have eq606 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq307 eq18 -- superposition 18,307, 307 into 18, unify on (0).2 in 307 and (0).2 in 18
  subsumption eq606 eq307


@[equational_result]
theorem Equation2462_implies_Equation205 (G : Type*) [Magma G] (h : Equation2462 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2462_implies_Equation2240 (G : Type*) [Magma G] (h : Equation2462 G) : Equation2240 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3007_implies_Equation255 (G : Type*) [Magma G] (h : Equation3007 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq16 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq16 rfl


@[equational_result]
theorem Equation3007_implies_Equation280 (G : Type*) [Magma G] (h : Equation3007 G) : Equation280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3105_implies_Equation2441 (G : Type*) [Magma G] (h : Equation3105 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation3254_implies_Equation307 (G : Type*) [Magma G] (h : Equation3254 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation474_implies_Equation3319 (G : Type*) [Magma G] (h : Equation474 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq14 -- forward demodulation 14,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq18 rfl


@[equational_result]
theorem Equation474_implies_Equation3253 (G : Type*) [Magma G] (h : Equation474 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 rfl


@[equational_result]
theorem Equation474_implies_Equation3862 (G : Type*) [Magma G] (h : Equation474 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 rfl


@[equational_result]
theorem Equation474_implies_Equation3915 (G : Type*) [Magma G] (h : Equation474 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq14 -- forward demodulation 14,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq18 rfl


@[equational_result]
theorem Equation474_implies_Equation1832 (G : Type*) [Magma G] (h : Equation474 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation474_implies_Equation1020 (G : Type*) [Magma G] (h : Equation474 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq17 eq16


@[equational_result]
theorem Equation474_implies_Equation8 (G : Type*) [Magma G] (h : Equation474 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation55_implies_Equation4065 (G : Type*) [Magma G] (h : Equation55 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation55_implies_Equation614 (G : Type*) [Magma G] (h : Equation55 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq8


@[equational_result]
theorem Equation55_implies_Equation817 (G : Type*) [Magma G] (h : Equation55 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.2 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation55_implies_Equation359 (G : Type*) [Magma G] (h : Equation55 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation3317_implies_Equation325 (G : Type*) [Magma G] (h : Equation3317 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3317_implies_Equation307 (G : Type*) [Magma G] (h : Equation3317 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.2 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation384_implies_Equation3862 (G : Type*) [Magma G] (h : Equation384 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq17 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq17 eq8


@[equational_result]
theorem Equation384_implies_Equation3659 (G : Type*) [Magma G] (h : Equation384 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).2.1 in 8
  have eq19 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq17 -- forward demodulation 17,8
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation384_implies_Equation3456 (G : Type*) [Magma G] (h : Equation384 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2338_implies_Equation1020 (G : Type*) [Magma G] (h : Equation2338 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq20 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq20 eq9 -- backward demodulation 9,20
  subsumption eq21 eq15


@[equational_result]
theorem Equation2338_implies_Equation1223 (G : Type*) [Magma G] (h : Equation2338 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq20 eq21 -- backward demodulation 21,20
  subsumption eq22 eq15


@[equational_result]
theorem Equation2338_implies_Equation614 (G : Type*) [Magma G] (h : Equation2338 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq18 eq9 -- backward demodulation 9,18
  subsumption eq21 eq15


@[equational_result]
theorem Equation2338_implies_Equation4380 (G : Type*) [Magma G] (h : Equation2338 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq23 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq23 rfl


