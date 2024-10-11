import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2812_implies_Equation231 (G : Type*) [Magma G] (h : Equation2812 G) : Equation231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation281_implies_Equation66 (G : Type*) [Magma G] (h : Equation281 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2.1 in 14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq18 eq13 -- backward demodulation 13,18
  have eq33 : sK0 ≠ sK0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq33 rfl


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
theorem Equation2836_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq42 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2836_implies_Equation246 (G : Type*) [Magma G] (h : Equation2836 G) : Equation246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2848_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2848 G) : Equation2690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).2 in 23
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.1 in 13
  have eq80 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2.1 in 10
  have eq106 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq47 eq47 -- superposition 47,47, 47 into 47, unify on (0).2 in 47 and (0).1.1.2 in 47
  have eq150 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq47 eq106 -- forward demodulation 106,47
  have eq151 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq150 -- forward demodulation 150,9
  have eq162 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X1) ◇ sK3) := superpose eq42 eq80 -- superposition 80,42, 42 into 80, unify on (0).2 in 42 and (0).2.1.1 in 80
  subsumption eq162 eq151


@[equational_result]
theorem Equation2850_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2850 G) : Equation2060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq13 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq26 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).1.1 in 13
  have eq64 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.1 in 10
  subsumption eq64 eq26


@[equational_result]
theorem Equation2850_implies_Equation4656 (G : Type*) [Magma G] (h : Equation2850 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq64 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ X0) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq64 eq24


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
theorem Equation2858_implies_Equation2894 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq24 -- forward demodulation 24,9
  have eq52 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq37 -- superposition 37,9, 9 into 37, unify on (0).2 in 9 and (0).2.1 in 37
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq52 eq9 -- backward demodulation 9,52
  have eq87 : sK0 ≠ sK0 := superpose eq69 eq10 -- superposition 10,69, 69 into 10, unify on (0).2 in 69 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation2859_implies_Equation262 (G : Type*) [Magma G] (h : Equation2859 G) : Equation262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq38 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1 in 10
  subsumption eq38 eq21


@[equational_result]
theorem Equation2860_implies_Equation2062 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2062 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq52 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) := superpose eq52 eq12 -- superposition 12,52, 52 into 12, unify on (0).2 in 52 and (0).1.2 in 12
  have eq102 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq52 eq93 -- forward demodulation 93,52
  have eq376 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ X0) ◇ (sK0 ◇ sK2)) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2.1 in 10
  subsumption eq376 eq102


@[equational_result]
theorem Equation2860_implies_Equation261 (G : Type*) [Magma G] (h : Equation2860 G) : Equation261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq365 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.1 in 11
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq557 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq432 eq365 -- forward demodulation 365,432
  have eq558 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq309 eq557 -- forward demodulation 557,309
  have eq559 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq558 eq10 -- backward demodulation 10,558
  subsumption eq559 eq150


@[equational_result]
theorem Equation2860_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq465 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq432 eq407 -- backward demodulation 407,432
  have eq476 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq465 eq10 -- backward demodulation 10,465
  subsumption eq476 eq49


@[equational_result]
theorem Equation2860_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq30 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq52 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1.1.2 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq144 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0))) := superpose eq86 eq11 -- superposition 11,86, 86 into 11, unify on (0).2 in 86 and (0).2.1 in 11
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq175 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq26 eq15 -- superposition 15,26, 26 into 15, unify on (0).2 in 26 and (0).1.2 in 15
  have eq207 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) := superpose eq175 eq52 -- backward demodulation 52,175
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq440 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq432 eq30 -- backward demodulation 30,432
  have eq447 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq432 eq48 -- backward demodulation 48,432
  have eq457 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0))) := superpose eq432 eq144 -- backward demodulation 144,432
  have eq465 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq432 eq407 -- backward demodulation 407,432
  have eq467 (X0 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) := superpose eq402 eq440 -- forward demodulation 440,402
  have eq598 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq49 eq432 -- superposition 432,49, 49 into 432, unify on (0).2 in 49 and (0).1.2 in 432
  have eq610 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq49 eq598 -- forward demodulation 598,49
  have eq631 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq86 eq467 -- superposition 467,86, 86 into 467, unify on (0).2 in 86 and (0).2 in 467
  have eq650 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq631 eq457 -- backward demodulation 457,631
  have eq684 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) := superpose eq42 eq447 -- superposition 447,42, 42 into 447, unify on (0).2 in 42 and (0).2.2.1 in 447
  have eq706 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) := superpose eq650 eq684 -- forward demodulation 684,650
  have eq1368 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq207 eq465 -- superposition 465,207, 207 into 465, unify on (0).2 in 207 and (0).2.2 in 465
  have eq1479 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq432 eq1368 -- forward demodulation 1368,432
  have eq1480 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq650 eq1479 -- forward demodulation 1479,650
  have eq1481 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq610 eq1480 -- forward demodulation 1480,610
  have eq1482 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq706 eq1481 -- forward demodulation 1481,706
  have eq1483 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose eq1482 eq10 -- backward demodulation 10,1482
  subsumption eq1483 eq150


@[equational_result]
theorem Equation2860_implies_Equation308 (G : Type*) [Magma G] (h : Equation2860 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq143 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq144 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq144 eq19 -- superposition 19,144, 144 into 19, unify on (0).2 in 144 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq26 -- superposition 26,144, 144 into 26, unify on (0).2 in 144 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq144 eq42 -- superposition 42,144, 144 into 42, unify on (0).2 in 144 and (0).1.1 in 42
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq143 eq412 -- forward demodulation 412,143
  have eq605 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq432 eq10 -- superposition 10,432, 432 into 10, unify on (0).2 in 432 and (0).1 in 10
  subsumption eq605 rfl


@[equational_result]
theorem Equation2860_implies_Equation3457 (G : Type*) [Magma G] (h : Equation2860 G) : Equation3457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq1209 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq1209 rfl


@[equational_result]
theorem Equation2860_implies_Equation3458 (G : Type*) [Magma G] (h : Equation2860 G) : Equation3458 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq19 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := superpose eq15 eq17 -- forward demodulation 17,15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq26 eq26 -- superposition 26,26, 26 into 26, unify on (0).2 in 26 and (0).1 in 26
  have eq49 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq26 eq12 -- superposition 12,26, 26 into 12, unify on (0).2 in 26 and (0).2.2 in 12
  have eq86 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq49 eq49 -- superposition 49,49, 49 into 49, unify on (0).2 in 49 and (0).1.1 in 49
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq86 eq12 -- superposition 12,86, 86 into 12, unify on (0).2 in 86 and (0).1 in 12
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq86 eq9 -- superposition 9,86, 86 into 9, unify on (0).2 in 86 and (0).1.1.1 in 9
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq150 eq19 -- superposition 19,150, 150 into 19, unify on (0).2 in 150 and (0).1.1.1.2 in 19
  have eq235 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq26 -- superposition 26,150, 150 into 26, unify on (0).2 in 150 and (0).1.1.2 in 26
  have eq309 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq150 eq42 -- superposition 42,150, 150 into 42, unify on (0).2 in 150 and (0).1.1 in 42
  have eq365 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).2.1 in 11
  have eq402 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq309 eq235 -- backward demodulation 235,309
  have eq404 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq402 eq234 -- backward demodulation 234,402
  have eq407 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq404 eq15 -- backward demodulation 15,404
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq407 eq54 -- backward demodulation 54,407
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq149 eq412 -- forward demodulation 412,149
  have eq557 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = (((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X0) := superpose eq432 eq365 -- forward demodulation 365,432
  have eq558 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq309 eq557 -- forward demodulation 557,309
  have eq559 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq558 eq10 -- backward demodulation 10,558
  subsumption eq559 eq149


@[equational_result]
theorem Equation2861_implies_Equation2881 (G : Type*) [Magma G] (h : Equation2861 G) : Equation2881 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ X0)) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq32 eq9


@[equational_result]
theorem Equation2862_implies_Equation255 (G : Type*) [Magma G] (h : Equation2862 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2864_implies_Equation2861 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq57 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq61 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq61 eq57


@[equational_result]
theorem Equation2867_implies_Equation2693 (G : Type*) [Magma G] (h : Equation2867 G) : Equation2693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X3 ◇ X0)) ◇ X3) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq32 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq33 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq17 -- forward demodulation 17,9
  have eq95 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK2) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1 in 10
  subsumption eq95 eq33


@[equational_result]
theorem Equation2868_implies_Equation257 (G : Type*) [Magma G] (h : Equation2868 G) : Equation257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2869_implies_Equation2851 (G : Type*) [Magma G] (h : Equation2869 G) : Equation2851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq71 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq71 eq22


@[equational_result]
theorem Equation2870_implies_Equation2896 (G : Type*) [Magma G] (h : Equation2870 G) : Equation2896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq29 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq45 (X0 : G) : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq45 eq29


@[equational_result]
theorem Equation2877_implies_Equation2058 (G : Type*) [Magma G] (h : Equation2877 G) : Equation2058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq35 (X0 X2 X4 : G) : (X0 ◇ X2) = (X0 ◇ X4) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq36 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X0 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq104 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq104 eq36


@[equational_result]
theorem Equation2879_implies_Equation2651 (G : Type*) [Magma G] (h : Equation2879 G) : Equation2651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq28 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq28 eq21


@[equational_result]
theorem Equation2881_implies_Equation2885 (G : Type*) [Magma G] (h : Equation2881 G) : Equation2885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2883_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2883 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq19 (X0 X1 X4 : G) : (((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X4 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq27 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ X4) = ((X4 ◇ ((X4 ◇ X0) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq94 (X0 X1 X3 X4 : G) : ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) = ((X3 ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq27 eq12 -- superposition 12,27, 27 into 12, unify on (0).2 in 27 and (0).1.1.2.1 in 12
  have eq124 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq19 eq16 -- superposition 16,19, 19 into 16, unify on (0).2 in 19 and (0).1.1 in 16
  have eq334 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).1.1 in 9
  have eq414 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X1 ◇ (X3 ◇ X4))) := superpose eq124 eq21 -- superposition 21,124, 124 into 21, unify on (0).2 in 124 and (0).2.1 in 21
  have eq499 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X3) := superpose eq414 eq94 -- backward demodulation 94,414
  have eq1750 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X4)) := superpose eq11 eq334 -- superposition 334,11, 11 into 334, unify on (0).2 in 11 and (0).2.2.1 in 334
  have eq2717 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq499 eq11 -- superposition 11,499, 499 into 11, unify on (0).2 in 499 and (0).1.1.1 in 11
  have eq2799 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X0)) := superpose eq1750 eq2717 -- forward demodulation 2717,1750
  have eq2800 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) := superpose eq11 eq2799 -- forward demodulation 2799,11
  have eq3261 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X2 ◇ (X0 ◇ X3)) := superpose eq19 eq2800 -- superposition 2800,19, 19 into 2800, unify on (0).2 in 19 and (0).2.2.1 in 2800
  have eq4729 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X4)) := superpose eq3261 eq3261 -- superposition 3261,3261, 3261 into 3261, unify on (0).2 in 3261 and (0).1 in 3261
  have eq6216 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq4729 eq10 -- superposition 10,4729, 4729 into 10, unify on (0).2 in 4729 and (0).2 in 10
  subsumption eq6216 eq4729


@[equational_result]
theorem Equation2884_implies_Equation2854 (G : Type*) [Magma G] (h : Equation2884 G) : Equation2854 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2887_implies_Equation2065 (G : Type*) [Magma G] (h : Equation2887 G) : Equation2065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq54 rfl


@[equational_result]
theorem Equation2890_implies_Equation263 (G : Type*) [Magma G] (h : Equation2890 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation2890_implies_Equation2649 (G : Type*) [Magma G] (h : Equation2890 G) : Equation2649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq47 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq48 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq100 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1.1 in 9
  have eq546 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq11 eq48 -- superposition 48,11, 11 into 48, unify on (0).2 in 11 and (0).1 in 48
  have eq911 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq12 eq546 -- superposition 546,12, 12 into 546, unify on (0).2 in 12 and (0).1.1.1.1 in 546
  have eq912 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq20 eq546 -- superposition 546,20, 20 into 546, unify on (0).2 in 20 and (0).1.1.1.1 in 546
  have eq1041 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq100 eq47 -- superposition 47,100, 100 into 47, unify on (0).2 in 100 and (0).1.1.1 in 47
  have eq1116 (X0 X1 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq11 eq1041 -- forward demodulation 1041,11
  have eq2066 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq911 eq1116 -- superposition 1116,911, 911 into 1116, unify on (0).2 in 911 and (0).1.1.1 in 1116
  have eq3735 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq2066 eq912 -- superposition 912,2066, 2066 into 912, unify on (0).2 in 2066 and (0).1.1.1.1.1 in 912
  have eq3779 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq3735 -- forward demodulation 3735,11
  have eq4087 : sK0 ≠ sK0 := superpose eq3779 eq10 -- superposition 10,3779, 3779 into 10, unify on (0).2 in 3779 and (0).2 in 10
  subsumption eq4087 rfl


@[equational_result]
theorem Equation2892_implies_Equation2680 (G : Type*) [Magma G] (h : Equation2892 G) : Equation2680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq22 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK1) := superpose eq16 eq22 -- superposition 22,16, 16 into 22, unify on (0).2 in 16 and (0).2.1 in 22
  subsumption eq32 eq23


@[equational_result]
theorem Equation2893_implies_Equation2671 (G : Type*) [Magma G] (h : Equation2893 G) : Equation2671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (((X4 ◇ X0) ◇ X3) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation266 (G : Type*) [Magma G] (h : Equation2894 G) : Equation266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2894_implies_Equation323 (G : Type*) [Magma G] (h : Equation2894 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X5) ◇ X4) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2898_implies_Equation2664 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (((X5 ◇ X0) ◇ X6) ◇ X7) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation2899_implies_Equation255 (G : Type*) [Magma G] (h : Equation2899 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


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
theorem Equation2905_implies_Equation2728 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK2 ◇ sK3) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2905_implies_Equation5 (G : Type*) [Magma G] (h : Equation2905 G) : Equation5 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


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
theorem Equation2911_implies_Equation996 (G : Type*) [Magma G] (h : Equation2911 G) : Equation996 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq15 : sK0 ≠ (sK1 ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).1 in 12
  have eq30 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2 in 15
  subsumption eq30 eq19


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
theorem Equation2915_implies_Equation2633 (G : Type*) [Magma G] (h : Equation2915 G) : Equation2633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2916_implies_Equation2010 (G : Type*) [Magma G] (h : Equation2916 G) : Equation2010 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq17


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
theorem Equation2919_implies_Equation2882 (G : Type*) [Magma G] (h : Equation2919 G) : Equation2882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


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
theorem Equation2922_implies_Equation1928 (G : Type*) [Magma G] (h : Equation2922 G) : Equation1928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X3 X5 : G) : ((X1 ◇ X3) ◇ X5) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq21 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq20


@[equational_result]
theorem Equation2923_implies_Equation2628 (G : Type*) [Magma G] (h : Equation2923 G) : Equation2628 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X3 ◇ X1) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X1 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2.1.2 in 12
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) = (((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5) ◇ ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((X4 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq34 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ ((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = X2 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ X0) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X4 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X5)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq11 eq25 -- superposition 25,11, 11 into 25, unify on (0).2 in 11 and (0).2.1.1 in 25
  have eq134 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X3)) ◇ X5)) ◇ X0) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1.2.1.2 in 12
  have eq136 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ X5) = ((((X3 ◇ (X0 ◇ X4)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X5 ◇ X0) ◇ X5)) := superpose eq13 eq25 -- superposition 25,13, 13 into 25, unify on (0).2 in 13 and (0).2.1.1 in 25
  have eq278 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((((X4 ◇ X1) ◇ X4) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X4 ◇ X1)) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.1.2.1 in 34
  have eq782 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X4)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq11 eq134 -- superposition 134,11, 11 into 134, unify on (0).2 in 11 and (0).1.1.2.1 in 134
  have eq1456 (X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = ((((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq27 eq278 -- superposition 278,27, 27 into 278, unify on (0).2 in 27 and (0).2.1.2 in 278
  have eq1457 (X1 X2 X3 X4 : G) : ((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) = (((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4)) := superpose eq27 eq52 -- superposition 52,27, 27 into 52, unify on (0).2 in 27 and (0).2.1 in 52
  have eq1459 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) ◇ X0) = X0 := superpose eq27 eq35 -- superposition 35,27, 27 into 35, unify on (0).2 in 27 and (0).1.1.2 in 35
  have eq1541 (X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = (((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq1457 eq1456 -- backward demodulation 1456,1457
  have eq1617 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq15 eq37 -- superposition 37,15, 15 into 37, unify on (0).2 in 15 and (0).2.1.2.1.2 in 37
  have eq1618 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((((((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq34 eq37 -- superposition 37,34, 34 into 37, unify on (0).2 in 34 and (0).2.1.2.1.2 in 37
  have eq1713 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq1617 -- forward demodulation 1617,11
  have eq1715 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = (((X4 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ X4) ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq11 eq1618 -- forward demodulation 1618,11
  have eq1900 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq24 eq1715 -- superposition 1715,24, 24 into 1715, unify on (0).2 in 24 and (0).2.1.1 in 1715
  have eq1911 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((((X4 ◇ X1) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X1)) ◇ X0)) ◇ (X4 ◇ X1)) := superpose eq1715 eq9 -- superposition 9,1715, 1715 into 9, unify on (0).2 in 1715 and (0).1.1.1 in 9
  have eq2388 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X4 ◇ X2) ◇ X4))) ◇ X5) = ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X5 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X4 ◇ X2) ◇ X4))) ◇ X5)) := superpose eq30 eq23 -- superposition 23,30, 30 into 23, unify on (0).2 in 30 and (0).1.1.2 in 23
  have eq2714 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq1713 eq25 -- superposition 25,1713, 1713 into 25, unify on (0).2 in 1713 and (0).2.1.1 in 25
  have eq2792 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X2 ◇ X0)) := superpose eq24 eq1911 -- superposition 1911,24, 24 into 1911, unify on (0).2 in 24 and (0).2.1.2.1 in 1911
  have eq2878 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3) = X3 := superpose eq11 eq1459 -- superposition 1459,11, 11 into 1459, unify on (0).2 in 11 and (0).1.1.2.1 in 1459
  have eq2937 (X2 X3 X5 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = (((X5 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X5) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) := superpose eq25 eq1541 -- superposition 1541,25, 25 into 1541, unify on (0).2 in 25 and (0).1 in 1541
  have eq2943 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X0) = X0 := superpose eq1541 eq9 -- superposition 9,1541, 1541 into 9, unify on (0).2 in 1541 and (0).1.1 in 9
  have eq3047 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq2937 eq2792 -- backward demodulation 2792,2937
  have eq3049 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq2937 eq1900 -- backward demodulation 1900,2937
  have eq3051 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq11 eq3047 -- forward demodulation 3047,11
  have eq3059 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X3 := superpose eq3049 eq2878 -- backward demodulation 2878,3049
  have eq3178 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq3051 eq2943 -- superposition 2943,3051, 3051 into 2943, unify on (0).2 in 3051 and (0).1.1 in 2943
  have eq3190 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq3051 eq23 -- superposition 23,3051, 3051 into 23, unify on (0).2 in 3051 and (0).1.1.2 in 23
  have eq3279 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X3 := superpose eq3178 eq3059 -- backward demodulation 3059,3178
  have eq3280 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = (((X4 ◇ X0) ◇ X4) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq3049 eq3190 -- forward demodulation 3190,3049
  have eq3288 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X4) = (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq3280 eq2714 -- backward demodulation 2714,3280
  have eq3370 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq3279 eq52 -- superposition 52,3279, 3279 into 52, unify on (0).2 in 3279 and (0).2.1 in 52
  have eq3371 (X0 X1 X3 : G) : (X3 ◇ X1) = ((((X3 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ X1)) := superpose eq3279 eq278 -- superposition 278,3279, 3279 into 278, unify on (0).2 in 3279 and (0).2.1.2 in 278
  have eq3383 (X0 X1 X3 : G) : (X3 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq3370 eq3371 -- forward demodulation 3371,3370
  have eq3406 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X4) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X4 ◇ X1) ◇ X4)) := superpose eq3383 eq3288 -- backward demodulation 3288,3383
  have eq3514 (X0 X1 X4 X5 : G) : (((X1 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq3406 eq782 -- backward demodulation 782,3406
  have eq3622 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5) = ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5)) := superpose eq3406 eq2388 -- backward demodulation 2388,3406
  have eq3778 (X1 X2 X4 X5 X6 : G) : ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5) = (((X6 ◇ X1) ◇ X6) ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X4)) ◇ X5)) := superpose eq3406 eq3622 -- forward demodulation 3622,3406
  have eq3781 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq3778 eq34 -- backward demodulation 34,3778
  have eq4610 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq3383 eq9 -- superposition 9,3383, 3383 into 9, unify on (0).2 in 3383 and (0).1.1 in 9
  have eq4765 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X4 ◇ X2)) := superpose eq3383 eq3781 -- superposition 3781,3383, 3383 into 3781, unify on (0).2 in 3383 and (0).2.1.1 in 3781
  have eq4974 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq4610 -- superposition 4610,12, 12 into 4610, unify on (0).2 in 12 and (0).1.1 in 4610
  have eq5059 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq4974 eq3049 -- backward demodulation 3049,4974
  have eq5128 (X0 X1 X2 X4 : G) : (X4 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ X2)) := superpose eq5059 eq4765 -- backward demodulation 4765,5059
  have eq5132 (X0 X1 X2 X5 : G) : ((X5 ◇ X0) ◇ X5) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ X0) ◇ X5)) := superpose eq5128 eq136 -- backward demodulation 136,5128
  have eq5633 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq5132 eq3514 -- backward demodulation 3514,5132
  have eq5932 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq3383 eq5633 -- superposition 5633,3383, 3383 into 5633, unify on (0).2 in 3383 and (0).1.1 in 5633
  have eq5955 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq5932 eq9 -- backward demodulation 9,5932
  have eq6754 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq5932 eq10 -- backward demodulation 10,5932
  subsumption eq6754 eq5955


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
theorem Equation2928_implies_Equation749 (G : Type*) [Magma G] (h : Equation2928 G) : Equation749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq25 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq25 eq13


@[equational_result]
theorem Equation2932_implies_Equation2307 (G : Type*) [Magma G] (h : Equation2932 G) : Equation2307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq25 eq20


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
theorem Equation2941_implies_Equation2976 (G : Type*) [Magma G] (h : Equation2941 G) : Equation2976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq42 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.1 in 10
  subsumption eq42 eq24


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
theorem Equation2957_implies_Equation470 (G : Type*) [Magma G] (h : Equation2957 G) : Equation470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1.2 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.1 in 9
  have eq54 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq40 -- forward demodulation 40,9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq54 eq23 -- backward demodulation 23,54
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq66 eq62 -- backward demodulation 62,66
  have eq70 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq66 eq13 -- backward demodulation 13,66
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq70 eq68 -- backward demodulation 68,70
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq71 eq9 -- backward demodulation 9,71
  have eq87 (X2 X3 : G) : X2 = X3 := superpose eq72 eq72 -- superposition 72,72, 72 into 72, unify on (0).2 in 72 and (0).1 in 72
  have eq93 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq72 eq10 -- superposition 10,72, 72 into 10, unify on (0).2 in 72 and (0).2 in 10
  subsumption eq93 eq87


@[equational_result]
theorem Equation2960_implies_Equation2525 (G : Type*) [Magma G] (h : Equation2960 G) : Equation2525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq28 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq30 : sK0 ≠ ((sK1 ◇ sK3) ◇ sK0) := superpose eq28 eq10 -- backward demodulation 10,28
  subsumption eq30 eq28


@[equational_result]
theorem Equation2973_implies_Equation3176 (G : Type*) [Magma G] (h : Equation2973 G) : Equation3176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2974_implies_Equation1683 (G : Type*) [Magma G] (h : Equation2974 G) : Equation1683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X3 ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq16 eq13 -- backward demodulation 13,16
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq21 eq10 -- backward demodulation 10,21
  subsumption eq27 eq21


@[equational_result]
theorem Equation2975_implies_Equation2976 (G : Type*) [Magma G] (h : Equation2975 G) : Equation2976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK3) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation2977_implies_Equation2509 (G : Type*) [Magma G] (h : Equation2977 G) : Equation2509 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq62 : sK0 ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq62 eq34


@[equational_result]
theorem Equation2979_implies_Equation746 (G : Type*) [Magma G] (h : Equation2979 G) : Equation746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ X2) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq11 eq33 -- superposition 33,11, 11 into 33, unify on (0).2 in 11 and (0).1 in 33
  have eq96 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).1.2.2 in 35
  have eq237 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq96 eq49 -- superposition 49,96, 96 into 49, unify on (0).2 in 96 and (0).1.1 in 49
  have eq867 : sK0 ≠ sK0 := superpose eq237 eq10 -- superposition 10,237, 237 into 10, unify on (0).2 in 237 and (0).2 in 10
  subsumption eq867 rfl


@[equational_result]
theorem Equation2982_implies_Equation749 (G : Type*) [Magma G] (h : Equation2982 G) : Equation749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.2 in 16
  have eq76 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq50 eq16 -- backward demodulation 16,50
  have eq79 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := superpose eq50 eq10 -- backward demodulation 10,50
  subsumption eq79 eq76


@[equational_result]
theorem Equation2983_implies_Equation1294 (G : Type*) [Magma G] (h : Equation2983 G) : Equation1294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq24 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (((X0 ◇ X1) ◇ X1) ◇ sK3)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.1 in 10
  subsumption eq24 eq16


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
theorem Equation2994_implies_Equation283 (G : Type*) [Magma G] (h : Equation2994 G) : Equation283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2998_implies_Equation3011 (G : Type*) [Magma G] (h : Equation2998 G) : Equation3011 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ X3) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq46 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq9 eq35 -- forward demodulation 35,9
  have eq57 (X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq46 eq31 -- backward demodulation 31,46
  have eq96 : sK0 ≠ sK0 := superpose eq57 eq10 -- superposition 10,57, 57 into 10, unify on (0).2 in 57 and (0).2 in 10
  subsumption eq96 rfl


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
theorem Equation3009_implies_Equation475 (G : Type*) [Magma G] (h : Equation3009 G) : Equation475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X1 X2 : G) : X1 = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq17 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq17 eq15


@[equational_result]
theorem Equation3015_implies_Equation2720 (G : Type*) [Magma G] (h : Equation3015 G) : Equation2720 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


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
theorem Equation3051_implies_Equation3082 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq13 (X0 X1 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1.1 in 11
  have eq17 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq19 -- forward demodulation 19,9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq20 eq20 -- superposition 20,20, 20 into 20, unify on (0).2 in 20 and (0).2 in 20
  have eq72 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK1) ◇ sK2) ◇ sK1) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2.1.1.1 in 10
  have eq164 : sK0 ≠ ((((sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ sK2) ◇ sK1) := superpose eq17 eq72 -- superposition 72,17, 17 into 72, unify on (0).2 in 17 and (0).2.1.1 in 72
  have eq171 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq11 eq164 -- forward demodulation 164,11
  subsumption eq171 eq9


@[equational_result]
theorem Equation3053_implies_Equation3083 (G : Type*) [Magma G] (h : Equation3053 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation3057_implies_Equation3073 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.1 in 9
  have eq39 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK2) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1.1 in 13
  subsumption eq39 eq36


@[equational_result]
theorem Equation3059_implies_Equation3078 (G : Type*) [Magma G] (h : Equation3059 G) : Equation3078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq17 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.2 in 13
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1.1 in 12
  have eq27 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq30 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq20 eq27 -- backward demodulation 27,20
  have eq66 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1.1.1 in 9
  have eq73 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq66 eq10 -- backward demodulation 10,66
  subsumption eq73 eq9


@[equational_result]
theorem Equation3059_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3059 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.1.1 in 8
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq15 -- forward demodulation 15,10
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1.1 in 11
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq19 eq12 -- backward demodulation 12,19
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation3061_implies_Equation3097 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3097 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq37 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).1.1 in 9
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq37 eq9 -- superposition 9,37, 37 into 9, unify on (0).2 in 37 and (0).1.1.1 in 9
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := superpose eq76 eq37 -- superposition 37,76, 76 into 37, unify on (0).2 in 76 and (0).1.1 in 37
  have eq326 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq221 eq11 -- superposition 11,221, 221 into 11, unify on (0).2 in 221 and (0).1 in 11
  have eq492 : sK0 ≠ sK0 := superpose eq326 eq10 -- superposition 10,326, 326 into 10, unify on (0).2 in 326 and (0).2 in 10
  subsumption eq492 rfl


@[equational_result]
theorem Equation3062_implies_Equation3101 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK3) ◇ sK4) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK3) ◇ sK4) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3063_implies_Equation3072 (G : Type*) [Magma G] (h : Equation3063 G) : Equation3072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq37 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK1) := superpose eq14 eq13 -- superposition 13,14, 14 into 13, unify on (0).2 in 14 and (0).2.1.1 in 13
  subsumption eq37 eq21


@[equational_result]
theorem Equation3063_implies_Equation38 (G : Type*) [Magma G] (h : Equation3063 G) : Equation38 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation3070_implies_Equation3098 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK3) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X4) ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X4) ◇ X5) := superpose eq11 eq31 -- forward demodulation 31,11
  have eq55 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq9 eq54 -- forward demodulation 54,9
  have eq56 (X0 X3 X5 : G) : (X0 ◇ X3) = (X0 ◇ X5) := superpose eq9 eq55 -- forward demodulation 55,9
  have eq80 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq56 eq9 -- superposition 9,56, 56 into 9, unify on (0).2 in 56 and (0).1.1.1.1 in 9
  have eq93 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK3) ◇ X0) := superpose eq56 eq13 -- superposition 13,56, 56 into 13, unify on (0).2 in 56 and (0).2 in 13
  subsumption eq93 eq80


@[equational_result]
theorem Equation3071_implies_Equation323 (G : Type*) [Magma G] (h : Equation3071 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation3072_implies_Equation3062 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3062 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq25 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq57 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq27 eq25 -- backward demodulation 25,27
  have eq97 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK2) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq97 eq57


@[equational_result]
theorem Equation3073_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3073 G) : Equation3084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq42 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq105 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X3) ◇ X3) := superpose eq98 eq11 -- backward demodulation 11,98
  have eq159 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ X4) = ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X3) := superpose eq105 eq105 -- superposition 105,105, 105 into 105, unify on (0).2 in 105 and (0).1.1 in 105
  have eq160 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq14 eq105 -- superposition 105,14, 14 into 105, unify on (0).2 in 14 and (0).1 in 105
  have eq199 (X1 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X1) ◇ X1) ◇ sK3) := superpose eq105 eq42 -- superposition 42,105, 105 into 42, unify on (0).2 in 105 and (0).2.1 in 42
  have eq218 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq160 eq159 -- backward demodulation 159,160
  subsumption eq199 eq218


@[equational_result]
theorem Equation3077_implies_Equation3080 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq34 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq88 (X0 : G) : sK0 ≠ ((((sK0 ◇ X0) ◇ X0) ◇ sK1) ◇ sK2) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1.1 in 15
  subsumption eq88 eq34


@[equational_result]
theorem Equation3078_implies_Equation307 (G : Type*) [Magma G] (h : Equation3078 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation3081_implies_Equation3061 (G : Type*) [Magma G] (h : Equation3081 G) : Equation3061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1.1 in 9
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.1.1 in 27
  have eq149 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X0 := superpose eq35 eq17 -- superposition 17,35, 35 into 17, unify on (0).2 in 35 and (0).1.1 in 17
  have eq253 : sK0 ≠ sK0 := superpose eq149 eq10 -- superposition 10,149, 149 into 10, unify on (0).2 in 149 and (0).2 in 10
  subsumption eq253 rfl


@[equational_result]
theorem Equation3082_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq58 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X2) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq62 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK1) ◇ sK3) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  have eq71 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq31 -- forward demodulation 31,9
  have eq76 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X1) ◇ X2) = X0 := superpose eq71 eq58 -- forward demodulation 58,71
  subsumption eq62 eq76


@[equational_result]
theorem Equation3083_implies_Equation3094 (G : Type*) [Magma G] (h : Equation3083 G) : Equation3094 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq28 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq28 eq26


@[equational_result]
theorem Equation3084_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.1 in 9
  have eq24 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK1) ◇ X0) ◇ sK2) ◇ sK3) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq24 eq21


@[equational_result]
theorem Equation3086_implies_Equation3060 (G : Type*) [Magma G] (h : Equation3086 G) : Equation3060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.1 in 30
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X0) := superpose eq36 eq12 -- backward demodulation 12,36
  have eq67 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq36 eq36 -- superposition 36,36, 36 into 36, unify on (0).2 in 36 and (0).2 in 36
  have eq159 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq84 eq30 -- superposition 30,84, 84 into 30, unify on (0).2 in 84 and (0).1.1 in 30
  have eq167 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ X0) ◇ sK2) := superpose eq84 eq67 -- superposition 67,84, 84 into 67, unify on (0).2 in 84 and (0).2.1 in 67
  subsumption eq167 eq159


@[equational_result]
theorem Equation3087_implies_Equation3077 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq22 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq40 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ sK0) ◇ sK2) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1.1 in 15
  subsumption eq40 eq22


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
  have eq7698 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) ◇ X0) = X0 := superpose eq437 eq9 -- superposition 9,437, 437 into 9, unify on (0).2 in 437 and (0).1.1 in 9
  have eq8486 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2)) := superpose eq7698 eq9 -- superposition 9,7698, 7698 into 9, unify on (0).2 in 7698 and (0).1.1 in 9
  have eq8490 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = ((X0 ◇ (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) ◇ X3)) := superpose eq8486 eq439 -- backward demodulation 439,8486
  have eq8694 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq17 eq8490 -- superposition 8490,17, 17 into 8490, unify on (0).2 in 17 and (0).1.1.1 in 8490
  have eq9004 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq8694 eq9 -- superposition 9,8694, 8694 into 9, unify on (0).2 in 8694 and (0).1.1.1 in 9
  have eq9015 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9004 -- forward demodulation 9004,12
  have eq9116 : sK0 ≠ sK0 := superpose eq9015 eq10 -- superposition 10,9015, 9015 into 10, unify on (0).2 in 9015 and (0).2 in 10
  subsumption eq9116 rfl


@[equational_result]
theorem Equation3090_implies_Equation3063 (G : Type*) [Magma G] (h : Equation3090 G) : Equation3063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq15 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq23 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).2 in 15
  subsumption eq23 eq9


@[equational_result]
theorem Equation3093_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3093 G) : Equation3071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq205 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.1 in 47
  have eq265 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq9 eq205 -- superposition 205,9, 9 into 205, unify on (0).2 in 9 and (0).1 in 205
  have eq402 : sK0 ≠ sK0 := superpose eq265 eq10 -- superposition 10,265, 265 into 10, unify on (0).2 in 265 and (0).2 in 10
  subsumption eq402 rfl


@[equational_result]
theorem Equation3094_implies_Equation3053 (G : Type*) [Magma G] (h : Equation3094 G) : Equation3053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ X0) ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq34 eq9


@[equational_result]
theorem Equation3094_implies_Equation4656 (G : Type*) [Magma G] (h : Equation3094 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq27 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq42 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose eq27 eq12 -- backward demodulation 12,27
  have eq90 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ X0) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq90 eq42


@[equational_result]
theorem Equation3095_implies_Equation3090 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq9


@[equational_result]
theorem Equation3103_implies_Equation1629 (G : Type*) [Magma G] (h : Equation3103 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation3103_implies_Equation8 (G : Type*) [Magma G] (h : Equation3103 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq13 rfl


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
theorem Equation3108_implies_Equation1038 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := superpose eq31 eq10 -- backward demodulation 10,31
  have eq33 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq32 -- forward demodulation 32,12
  subsumption eq33 eq13


@[equational_result]
theorem Equation3108_implies_Equation1225 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1225 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation3108_implies_Equation1441 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq15 -- forward demodulation 15,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3108_implies_Equation1664 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq27 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq27 eq12


@[equational_result]
theorem Equation3108_implies_Equation1687 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq23 eq14 -- superposition 14,23, 23 into 14, unify on (0).2 in 23 and (0).2 in 14
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation1867 (G : Type*) [Magma G] (h : Equation3108 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq12


@[equational_result]
theorem Equation3108_implies_Equation221 (G : Type*) [Magma G] (h : Equation3108 G) : Equation221 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq22 eq12 -- superposition 12,22, 22 into 12, unify on (0).2 in 22 and (0).1.1 in 12
  have eq32 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq31 eq10 -- backward demodulation 10,31
  subsumption eq32 eq12


@[equational_result]
theorem Equation3108_implies_Equation228 (G : Type*) [Magma G] (h : Equation3108 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq32 : sK0 ≠ sK0 := superpose eq22 eq24 -- superposition 24,22, 22 into 24, unify on (0).2 in 22 and (0).2 in 24
  subsumption eq32 rfl


@[equational_result]
theorem Equation3108_implies_Equation2285 (G : Type*) [Magma G] (h : Equation3108 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 rfl


