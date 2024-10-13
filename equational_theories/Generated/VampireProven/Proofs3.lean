import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1662_implies_Equation2485 (G : Type*) [Magma G] (h : Equation1662 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1663_implies_Equation2463 (G : Type*) [Magma G] (h : Equation1663 G) : Equation2463 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq13


@[equational_result]
theorem Equation1666_implies_Equation2283 (G : Type*) [Magma G] (h : Equation1666 G) : Equation2283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.1 in 11
  have eq81 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2.1 in 11
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq11 eq81 -- superposition 81,11, 11 into 81, unify on (0).2 in 11 and (0).1.1 in 81
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq115 eq9 -- backward demodulation 9,115
  have eq183 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq115 eq94 -- backward demodulation 94,115
  have eq212 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq115 eq183 -- forward demodulation 183,115
  have eq213 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq172 eq212 -- forward demodulation 212,172
  have eq216 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq213 eq10 -- backward demodulation 10,213
  subsumption eq216 eq172


@[equational_result]
theorem Equation1668_implies_Equation1875 (G : Type*) [Magma G] (h : Equation1668 G) : Equation1875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ (X4 ◇ X3)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1669_implies_Equation2275 (G : Type*) [Magma G] (h : Equation1669 G) : Equation2275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq24 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1 in 23
  have eq37 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq37 eq24


@[equational_result]
theorem Equation1670_implies_Equation2482 (G : Type*) [Magma G] (h : Equation1670 G) : Equation2482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq109 : sK0 ≠ sK0 := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation1670_implies_Equation3334 (G : Type*) [Magma G] (h : Equation1670 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq84 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq84 rfl


@[equational_result]
theorem Equation1676_implies_Equation1879 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1683_implies_Equation755 (G : Type*) [Magma G] (h : Equation1683 G) : Equation755 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK3) ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq17 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq20 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := superpose eq17 eq16 -- backward demodulation 16,17
  have eq24 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq17 eq19 -- forward demodulation 19,17
  have eq25 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq24 eq20 -- backward demodulation 20,24
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq25 eq14 -- backward demodulation 14,25
  have eq30 : sK0 ≠ (sK1 ◇ sK2) := superpose eq25 eq15 -- backward demodulation 15,25
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq25 eq28 -- forward demodulation 28,25
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq31 eq25 -- superposition 25,31, 31 into 25, unify on (0).2 in 31 and (0).1 in 25
  have eq34 : sK0 ≠ sK1 := superpose eq25 eq30 -- superposition 30,25, 25 into 30, unify on (0).2 in 25 and (0).2 in 30
  subsumption eq34 eq33


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
theorem Equation1688_implies_Equation2806 (G : Type*) [Magma G] (h : Equation1688 G) : Equation2806 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq18 eq25 -- forward demodulation 25,18
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) = X0 := superpose eq37 eq21 -- backward demodulation 21,37
  have eq46 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := superpose eq37 eq10 -- backward demodulation 10,37
  have eq47 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq37 eq38 -- forward demodulation 38,37
  have eq48 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq37 eq47 -- forward demodulation 47,37
  have eq49 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq18 eq48 -- forward demodulation 48,18
  have eq50 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X3)) = X1 := superpose eq49 eq12 -- backward demodulation 12,49
  have eq54 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq49 eq50 -- forward demodulation 50,49
  have eq55 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq49 eq54 -- forward demodulation 54,49
  have eq68 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq49 eq46 -- forward demodulation 46,49
  have eq69 : sK0 ≠ (sK0 ◇ sK2) := superpose eq49 eq68 -- forward demodulation 68,49
  subsumption eq69 eq55


@[equational_result]
theorem Equation169_implies_Equation1291 (G : Type*) [Magma G] (h : Equation169 G) : Equation1291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq18 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  subsumption eq18 eq13


@[equational_result]
theorem Equation1695_implies_Equation1932 (G : Type*) [Magma G] (h : Equation1695 G) : Equation1932 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1.1 in 11
  have eq19 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq67 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1.2 in 22
  have eq100 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).1 in 19
  have eq157 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq67 eq67 -- superposition 67,67, 67 into 67, unify on (0).2 in 67 and (0).1.1 in 67
  have eq158 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq67 eq22 -- superposition 22,67, 67 into 22, unify on (0).2 in 67 and (0).1.1 in 22
  have eq165 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq100 eq158 -- forward demodulation 158,100
  have eq166 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq9 eq165 -- forward demodulation 165,9
  have eq397 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq157 eq166 -- superposition 166,157, 157 into 166, unify on (0).2 in 157 and (0).1.2.2 in 166
  have eq548 : sK0 ≠ sK0 := superpose eq397 eq10 -- superposition 10,397, 397 into 10, unify on (0).2 in 397 and (0).2 in 10
  subsumption eq548 rfl


@[equational_result]
theorem Equation1696_implies_Equation979 (G : Type*) [Magma G] (h : Equation1696 G) : Equation979 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq20 : sK0 ≠ (sK1 ◇ sK2) := superpose eq17 eq10 -- backward demodulation 10,17
  have eq25 (X0 X1 : G) : X0 = X1 := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).1 in 17
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq20 -- superposition 20,25, 25 into 20, unify on (0).2 in 25 and (0).2 in 20
  subsumption eq35 eq25


@[equational_result]
theorem Equation1697_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1697_implies_Equation1867 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq961 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq913 -- forward demodulation 913,323
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1697_implies_Equation2161 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq441 : sK0 ≠ sK0 := superpose eq323 eq10 -- superposition 10,323, 323 into 10, unify on (0).2 in 323 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1697_implies_Equation2165 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2165 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).1.2 in 9
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.1 in 164
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq50 eq15 -- superposition 15,50, 50 into 15, unify on (0).2 in 50 and (0).1.2 in 15
  have eq929 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq224 eq13 -- superposition 13,224, 224 into 13, unify on (0).2 in 224 and (0).2.1 in 13
  have eq963 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq323 eq929 -- forward demodulation 929,323
  have eq1132 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq963 eq9 -- superposition 9,963, 963 into 9, unify on (0).2 in 963 and (0).1.2.1 in 9
  have eq2222 : sK0 ≠ sK0 := superpose eq1132 eq10 -- superposition 10,1132, 1132 into 10, unify on (0).2 in 1132 and (0).2 in 10
  subsumption eq2222 rfl


@[equational_result]
theorem Equation1697_implies_Equation2169 (G : Type*) [Magma G] (h : Equation1697 G) : Equation2169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1697_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1697 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq76 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).2.2 in 11
  have eq598 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq598 rfl


@[equational_result]
theorem Equation1697_implies_Equation4083 (G : Type*) [Magma G] (h : Equation1697 G) : Equation4083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq50 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2.1 in 13
  have eq327 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2 in 10
  subsumption eq327 rfl


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
theorem Equation170_implies_Equation177 (G : Type*) [Magma G] (h : Equation170 G) : Equation177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.2.2 in 21
  have eq50 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq50 rfl


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
theorem Equation170_implies_Equation47 (G : Type*) [Magma G] (h : Equation170 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq16 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2.1 in 10
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq26 : sK0 ≠ sK0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation1705_implies_Equation2053 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation2087 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation2127 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation2169 (G : Type*) [Magma G] (h : Equation1705 G) : Equation2169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.1 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1705_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1705 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq113 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq113 rfl


@[equational_result]
theorem Equation170_implies_Equation66 (G : Type*) [Magma G] (h : Equation170 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq29 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1706_implies_Equation890 (G : Type*) [Magma G] (h : Equation1706 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X2 ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = (X3 ◇ ((X4 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X0) ◇ ((X4 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1.2 in 11
  have eq41 (X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X2) = ((X4 ◇ X2) ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2 in 11
  have eq53 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = (((X4 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).1.1 in 13
  have eq54 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq22 eq23 -- forward demodulation 23,22
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq54 eq15 -- backward demodulation 15,54
  have eq58 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq57 eq11 -- backward demodulation 11,57
  have eq79 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X1) = (((X2 ◇ X0) ◇ X0) ◇ ((X4 ◇ X1) ◇ X1)) := superpose eq57 eq34 -- forward demodulation 34,57
  have eq109 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = ((X3 ◇ X1) ◇ X1) := superpose eq79 eq53 -- forward demodulation 53,79
  have eq110 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq54 eq109 -- forward demodulation 109,54
  have eq111 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X3 ◇ X1) ◇ X1) := superpose eq54 eq110 -- forward demodulation 110,54
  have eq132 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq41 eq13 -- superposition 13,41, 41 into 13, unify on (0).2 in 41 and (0).1.1 in 13
  have eq148 (X1 X3 : G) : ((X3 ◇ X1) ◇ X1) = X1 := superpose eq132 eq111 -- backward demodulation 111,132
  have eq149 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq148 eq9 -- backward demodulation 9,148
  have eq153 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq148 eq54 -- backward demodulation 54,148
  have eq155 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq148 eq58 -- backward demodulation 58,148
  have eq170 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq153 eq149 -- backward demodulation 149,153
  have eq173 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq153 eq10 -- backward demodulation 10,153
  have eq174 : sK0 ≠ (sK1 ◇ sK1) := superpose eq153 eq173 -- forward demodulation 173,153
  have eq176 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq153 eq155 -- forward demodulation 155,153
  have eq190 (X0 X1 : G) : X0 = X1 := superpose eq170 eq176 -- superposition 176,170, 170 into 176, unify on (0).2 in 170 and (0).1 in 176
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq176 eq174 -- superposition 174,176, 176 into 174, unify on (0).2 in 176 and (0).2 in 174
  subsumption eq193 eq190


@[equational_result]
theorem Equation1707_implies_Equation4647 (G : Type*) [Magma G] (h : Equation1707 G) : Equation4647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK2 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = ((X4 ◇ X2) ◇ X4) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2 in 11
  have eq73 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ ((X0 ◇ sK1) ◇ X0) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).1 in 10
  subsumption eq73 eq24


@[equational_result]
theorem Equation1709_implies_Equation2156 (G : Type*) [Magma G] (h : Equation1709 G) : Equation2156 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq33 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK3 ◇ sK0)) := superpose eq26 eq10 -- backward demodulation 10,26
  have eq53 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq26 -- superposition 26,12, 12 into 26, unify on (0).2 in 12 and (0).1 in 26
  have eq55 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X2) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).2.1 in 26
  have eq87 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq55 eq33 -- backward demodulation 33,55
  subsumption eq87 eq53


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
theorem Equation1724_implies_Equation3288 (G : Type*) [Magma G] (h : Equation1724 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X0 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq201 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq195 -- forward demodulation 195,11
  have eq321 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.2 in 10
  subsumption eq321 eq255


@[equational_result]
theorem Equation1734_implies_Equation1175 (G : Type*) [Magma G] (h : Equation1734 G) : Equation1175 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq26 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK2 ◇ X0) ◇ sK0)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.2 in 13
  have eq31 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq47 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X3 := superpose eq34 eq31 -- backward demodulation 31,34
  have eq49 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq47 eq11 -- backward demodulation 11,47
  have eq72 : sK0 ≠ sK0 := superpose eq49 eq26 -- superposition 26,49, 49 into 26, unify on (0).2 in 49 and (0).2 in 26
  subsumption eq72 rfl


@[equational_result]
theorem Equation1738_implies_Equation107 (G : Type*) [Magma G] (h : Equation1738 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq25 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ sK0) ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  have eq29 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  subsumption eq25 eq29


@[equational_result]
theorem Equation1738_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1738 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq22 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  have eq29 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq31 (X1 : G) : sK0 ≠ (sK0 ◇ ((X1 ◇ sK0) ◇ sK0)) := superpose eq12 eq22 -- superposition 22,12, 12 into 22, unify on (0).2 in 12 and (0).2.2 in 22
  subsumption eq31 eq29


@[equational_result]
theorem Equation1738_implies_Equation4619 (G : Type*) [Magma G] (h : Equation1738 G) : Equation4619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = ((X3 ◇ X3) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq18


@[equational_result]
theorem Equation1750_implies_Equation1806 (G : Type*) [Magma G] (h : Equation1750 G) : Equation1806 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq30 rfl


@[equational_result]
theorem Equation1755_implies_Equation1900 (G : Type*) [Magma G] (h : Equation1755 G) : Equation1900 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (X2 ◇ ((X3 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq11 eq15 -- forward demodulation 15,11
  have eq56 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq22 eq11 -- superposition 11,22, 22 into 11, unify on (0).2 in 22 and (0).1.2 in 11
  have eq67 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq56 eq10 -- backward demodulation 10,56
  subsumption eq67 eq56


@[equational_result]
theorem Equation1759_implies_Equation1927 (G : Type*) [Magma G] (h : Equation1759 G) : Equation1927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq24 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq24 eq16


@[equational_result]
theorem Equation1760_implies_Equation3027 (G : Type*) [Magma G] (h : Equation1760 G) : Equation3027 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq23 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK3) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq24 (X2 X3 : G) : X2 = X3 := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1 in 19
  have eq36 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq19 eq23 -- superposition 23,19, 19 into 23, unify on (0).2 in 19 and (0).2.1 in 23
  subsumption eq36 eq24


@[equational_result]
theorem Equation176_implies_Equation2178 (G : Type*) [Magma G] (h : Equation176 G) : Equation2178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1763_implies_Equation1202 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1202 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq20 (X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq32 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X3 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq13 -- superposition 13,32, 32 into 13, unify on (0).2 in 32 and (0).2.1 in 13
  have eq40 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq36 eq14 -- backward demodulation 14,36
  subsumption eq40 eq32


@[equational_result]
theorem Equation1765_implies_Equation2991 (G : Type*) [Magma G] (h : Equation1765 G) : Equation2991 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq41 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X4 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))))) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq47 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq17 eq41 -- forward demodulation 41,17
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).1 in 47
  have eq75 (X0 : G) : sK0 ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2.1 in 10
  subsumption eq75 eq48


@[equational_result]
theorem Equation177_implies_Equation170 (G : Type*) [Magma G] (h : Equation177 G) : Equation170 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq17 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1.1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.1.1 in 21
  have eq50 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1772_implies_Equation1750 (G : Type*) [Magma G] (h : Equation1772 G) : Equation1750 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X4) ◇ X4)) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.1 in 11
  have eq35 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq35 rfl


@[equational_result]
theorem Equation1789_implies_Equation1332 (G : Type*) [Magma G] (h : Equation1789 G) : Equation1332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq16 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ (X3 ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq30 (X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X3)) = ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq37 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.1 in 15
  have eq38 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.2 in 15
  have eq47 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq38 eq28 -- backward demodulation 28,38
  have eq48 (X0 X1 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ (X3 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3))) := superpose eq47 eq16 -- backward demodulation 16,47
  have eq64 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X3)) = ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X2 X3 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq92 (X0 X1 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ X3) := superpose eq90 eq48 -- backward demodulation 48,90
  have eq100 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ X3) := superpose eq90 eq92 -- forward demodulation 92,90
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq100 eq9 -- backward demodulation 9,100
  have eq107 (X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = X3 := superpose eq100 eq90 -- backward demodulation 90,100
  have eq110 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq100 eq10 -- backward demodulation 10,100
  have eq111 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq107 eq111 -- backward demodulation 111,107
  subsumption eq110 eq114


@[equational_result]
theorem Equation179_implies_Equation127 (G : Type*) [Magma G] (h : Equation179 G) : Equation127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation179_implies_Equation99 (G : Type*) [Magma G] (h : Equation179 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation1801_implies_Equation182 (G : Type*) [Magma G] (h : Equation1801 G) : Equation182 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X3 X4 X5 X6 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X6)) = X6 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : sK0 ≠ ((X0 ◇ X1) ◇ (sK2 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq37 eq14


@[equational_result]
theorem Equation1816_implies_Equation1096 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq42 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq36 eq13 -- superposition 13,36, 36 into 13, unify on (0).2 in 36 and (0).2.1 in 13
  have eq49 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq42 eq26 -- backward demodulation 26,42
  subsumption eq49 eq36


@[equational_result]
theorem Equation1816_implies_Equation2024 (G : Type*) [Magma G] (h : Equation1816 G) : Equation2024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ sK3)) ◇ (sK3 ◇ sK0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : sK0 ≠ (sK3 ◇ (sK3 ◇ sK0)) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1816_implies_Equation4040 (G : Type*) [Magma G] (h : Equation1816 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X5 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq26 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ (sK3 ◇ sK0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  have eq36 (X3 X5 : G) : (X3 ◇ (X3 ◇ X5)) = X5 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq52 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.1 in 26
  subsumption eq52 rfl


@[equational_result]
theorem Equation1816_implies_Equation4689 (G : Type*) [Magma G] (h : Equation1816 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq13


@[equational_result]
theorem Equation182_implies_Equation2217 (G : Type*) [Magma G] (h : Equation182 G) : Equation2217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1836_implies_Equation1433 (G : Type*) [Magma G] (h : Equation1836 G) : Equation1433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq50 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1 in 22
  have eq55 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).1.1 in 13
  have eq129 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq50 eq10 -- superposition 10,50, 50 into 10, unify on (0).2 in 50 and (0).2 in 10
  subsumption eq129 eq55


@[equational_result]
theorem Equation1842_implies_Equation1477 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq82 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq66 eq37 -- backward demodulation 37,66
  have eq85 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq82 -- forward demodulation 82,15
  have eq87 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq85 eq30 -- backward demodulation 30,85
  have eq91 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq87 -- forward demodulation 87,9
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq91 eq15 -- backward demodulation 15,91
  have eq102 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq94 eq9 -- backward demodulation 9,94
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq110 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq102 eq66 -- backward demodulation 66,102
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq108 eq110 -- backward demodulation 110,108
  have eq132 : sK0 ≠ sK0 := superpose eq113 eq10 -- superposition 10,113, 113 into 10, unify on (0).2 in 113 and (0).2 in 10
  subsumption eq132 rfl


@[equational_result]
theorem Equation1844_implies_Equation1669 (G : Type*) [Magma G] (h : Equation1844 G) : Equation1669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq31 (X0 X3 X4 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2.2 in 13
  have eq35 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq55 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X3) := superpose eq31 eq35 -- forward demodulation 35,31
  have eq155 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq55 eq31 -- superposition 31,55, 55 into 31, unify on (0).2 in 55 and (0).1.1 in 31
  have eq187 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq155 eq10 -- backward demodulation 10,155
  subsumption eq187 eq155


@[equational_result]
theorem Equation1845_implies_Equation211 (G : Type*) [Magma G] (h : Equation1845 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq28 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ X0)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  subsumption eq28 eq29


@[equational_result]
theorem Equation1845_implies_Equation2249 (G : Type*) [Magma G] (h : Equation1845 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq25 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X1 : G) : sK0 ≠ ((sK0 ◇ (sK0 ◇ X1)) ◇ sK0) := superpose eq12 eq25 -- superposition 25,12, 12 into 25, unify on (0).2 in 12 and (0).2.1 in 25
  subsumption eq32 eq29


@[equational_result]
theorem Equation1845_implies_Equation4288 (G : Type*) [Magma G] (h : Equation1845 G) : Equation4288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq28 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq28 eq21


@[equational_result]
theorem Equation1849_implies_Equation1430 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq68 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation1849_implies_Equation1431 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq53 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq53 eq40


@[equational_result]
theorem Equation1849_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2 in 27
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq40 eq42 -- superposition 42,40, 40 into 42, unify on (0).2 in 40 and (0).2 in 42
  have eq174 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq27 eq50 -- superposition 50,27, 27 into 50, unify on (0).2 in 27 and (0).1.1 in 50
  have eq208 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq42 eq174 -- forward demodulation 174,42
  have eq209 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq42 eq208 -- forward demodulation 208,42
  have eq210 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq91 eq209 -- forward demodulation 209,91
  have eq303 : sK0 ≠ sK0 := superpose eq210 eq10 -- superposition 10,210, 210 into 10, unify on (0).2 in 210 and (0).2 in 10
  subsumption eq303 rfl


@[equational_result]
theorem Equation1849_implies_Equation2243 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq40 -- forward demodulation 40,27
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq113 : sK0 ≠ sK0 := superpose eq93 eq44 -- superposition 44,93, 93 into 44, unify on (0).2 in 93 and (0).2 in 44
  subsumption eq113 rfl


@[equational_result]
theorem Equation1849_implies_Equation2443 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq37 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq38 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq27 eq12 -- backward demodulation 12,27
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq34 -- forward demodulation 34,11
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq37 -- forward demodulation 37,27
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq38 eq10 -- backward demodulation 10,38
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq40 -- superposition 40,43, 43 into 40, unify on (0).2 in 43 and (0).2 in 40
  have eq113 : sK0 ≠ sK0 := superpose eq93 eq44 -- superposition 44,93, 93 into 44, unify on (0).2 in 93 and (0).2 in 44
  subsumption eq113 rfl


@[equational_result]
theorem Equation1849_implies_Equation2476 (G : Type*) [Magma G] (h : Equation1849 G) : Equation2476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq40 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq41 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq35 -- forward demodulation 35,27
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq39 -- forward demodulation 39,11
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq43 -- superposition 43,41, 41 into 43, unify on (0).2 in 41 and (0).2 in 43
  have eq112 : sK0 ≠ sK0 := superpose eq92 eq40 -- superposition 40,92, 92 into 40, unify on (0).2 in 92 and (0).2 in 40
  subsumption eq112 rfl


@[equational_result]
theorem Equation1849_implies_Equation309 (G : Type*) [Magma G] (h : Equation1849 G) : Equation309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq55 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).1 in 10
  subsumption eq55 rfl


@[equational_result]
theorem Equation1849_implies_Equation4128 (G : Type*) [Magma G] (h : Equation1849 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq19 -- backward demodulation 19,27
  have eq37 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq35 -- forward demodulation 35,11
  have eq43 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq27 eq37 -- forward demodulation 37,27
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1.2 in 27
  have eq92 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq43 eq41 -- superposition 41,43, 43 into 41, unify on (0).2 in 43 and (0).2 in 41
  have eq174 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq51 eq51 -- superposition 51,51, 51 into 51, unify on (0).2 in 51 and (0).1.1 in 51
  have eq205 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq41 eq174 -- forward demodulation 174,41
  have eq206 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq92 eq205 -- forward demodulation 205,92
  have eq207 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq41 eq206 -- forward demodulation 206,41
  have eq208 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq11 eq207 -- forward demodulation 207,11
  have eq255 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq208 eq10 -- superposition 10,208, 208 into 10, unify on (0).2 in 208 and (0).2 in 10
  subsumption eq255 rfl


@[equational_result]
theorem Equation1852_implies_Equation2477 (G : Type*) [Magma G] (h : Equation1852 G) : Equation2477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X3 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq31 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X3 := superpose eq19 eq13 -- backward demodulation 13,19
  have eq35 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ X0) := superpose eq31 eq12 -- superposition 12,31, 31 into 12, unify on (0).2 in 31 and (0).2.2 in 12
  have eq39 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq39 eq31


@[equational_result]
theorem Equation1854_implies_Equation1878 (G : Type*) [Magma G] (h : Equation1854 G) : Equation1878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq26 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation1855_implies_Equation4069 (G : Type*) [Magma G] (h : Equation1855 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = ((X2 ◇ X2) ◇ (X3 ◇ X3)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq189 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ X3)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq201 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq255 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq11 eq189 -- forward demodulation 189,11
  have eq299 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq201 eq10 -- superposition 10,201, 201 into 10, unify on (0).2 in 201 and (0).2.1 in 10
  subsumption eq299 eq255


@[equational_result]
theorem Equation1859_implies_Equation1438 (G : Type*) [Magma G] (h : Equation1859 G) : Equation1438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2 in 26
  have eq61 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq33 eq10 -- backward demodulation 10,33
  have eq63 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq26 eq61 -- superposition 61,26, 26 into 61, unify on (0).2 in 26 and (0).2 in 61
  subsumption eq63 eq11


@[equational_result]
theorem Equation1868_implies_Equation1427 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1868_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1445 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1868_implies_Equation1446 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1446 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1868_implies_Equation4127 (G : Type*) [Magma G] (h : Equation1868 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq98 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1869_implies_Equation1430 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq317 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq47 eq16 -- superposition 16,47, 47 into 16, unify on (0).2 in 47 and (0).1.1 in 16
  have eq441 : sK0 ≠ sK0 := superpose eq317 eq10 -- superposition 10,317, 317 into 10, unify on (0).2 in 317 and (0).2 in 10
  subsumption eq441 rfl


@[equational_result]
theorem Equation1869_implies_Equation1448 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq942 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq963 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq942 -- forward demodulation 942,164
  have eq1132 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq963 eq9 -- superposition 9,963, 963 into 9, unify on (0).2 in 963 and (0).1.1.2 in 9
  have eq2222 : sK0 ≠ sK0 := superpose eq1132 eq10 -- superposition 10,1132, 1132 into 10, unify on (0).2 in 1132 and (0).2 in 10
  subsumption eq2222 rfl


@[equational_result]
theorem Equation1869_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq164 eq164 -- superposition 164,164, 164 into 164, unify on (0).2 in 164 and (0).1.2 in 164
  have eq913 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq234 eq12 -- superposition 12,234, 234 into 12, unify on (0).2 in 234 and (0).2.2 in 12
  have eq961 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq913 -- forward demodulation 913,164
  have eq1108 : sK0 ≠ sK0 := superpose eq961 eq10 -- superposition 10,961, 961 into 10, unify on (0).2 in 961 and (0).2 in 10
  subsumption eq1108 rfl


@[equational_result]
theorem Equation1869_implies_Equation1867 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1.1 in 17
  have eq164 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq9 -- superposition 9,41, 41 into 9, unify on (0).2 in 41 and (0).1.1 in 9
  have eq235 : sK0 ≠ sK0 := superpose eq164 eq10 -- superposition 10,164, 164 into 10, unify on (0).2 in 164 and (0).2 in 10
  subsumption eq235 rfl


@[equational_result]
theorem Equation1869_implies_Equation1868 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1869_implies_Equation3259 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3259 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).2.2 in 12
  have eq344 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq344 rfl


@[equational_result]
theorem Equation1869_implies_Equation3459 (G : Type*) [Magma G] (h : Equation1869 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq76 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).2.1 in 13
  have eq584 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq584 rfl


@[equational_result]
theorem Equation1870_implies_Equation1646 (G : Type*) [Magma G] (h : Equation1870 G) : Equation1646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq46 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq46 eq11


@[equational_result]
theorem Equation1871_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1657 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1871_implies_Equation1660 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1874_implies_Equation1633 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X0) = (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq26 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq36 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq52 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq36 eq26 -- superposition 26,36, 36 into 26, unify on (0).2 in 36 and (0).2.2 in 26
  subsumption eq52 eq36


@[equational_result]
theorem Equation1874_implies_Equation4357 (G : Type*) [Magma G] (h : Equation1874 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq30 eq12


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
theorem Equation1877_implies_Equation157 (G : Type*) [Magma G] (h : Equation1877 G) : Equation157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq43 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq48 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq43 eq11 -- backward demodulation 11,43
  have eq62 : sK0 ≠ sK0 := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq62 rfl


