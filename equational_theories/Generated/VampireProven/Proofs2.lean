import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1292_implies_Equation1683 (G : Type*) [Magma G] (h : Equation1292 G) : Equation1683 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq16


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
theorem Equation1296_implies_Equation2901 (G : Type*) [Magma G] (h : Equation1296 G) : Equation2901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq28 (X0 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq35 (X1 X3 : G) : X1 = X3 := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).1 in 28
  have eq61 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ X0)) ◇ sK2) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2.1 in 10
  subsumption eq61 eq35


@[equational_result]
theorem Equation1297_implies_Equation699 (G : Type*) [Magma G] (h : Equation1297 G) : Equation699 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq14 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X1 X3 : G) : X1 = X3 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).1 in 14
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  subsumption eq20 eq15


@[equational_result]
theorem Equation1299_implies_Equation1336 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1299_implies_Equation2078 (G : Type*) [Magma G] (h : Equation1299 G) : Equation2078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq12 -- backward demodulation 12,15
  have eq26 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation130_implies_Equation1759 (G : Type*) [Magma G] (h : Equation130 G) : Equation1759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1312_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1312 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1 in 8
  have eq52 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq52 rfl


@[equational_result]
theorem Equation1312_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1312 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2.1.1 in 8
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq21 -- forward demodulation 21,15
  have eq80 : sK0 ≠ sK0 := superpose eq26 eq9 -- superposition 9,26, 26 into 9, unify on (0).2 in 26 and (0).2 in 9
  subsumption eq80 rfl


@[equational_result]
theorem Equation1312_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1312 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq22 rfl


@[equational_result]
theorem Equation1312_implies_Equation8 (G : Type*) [Magma G] (h : Equation1312 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq11 -- forward demodulation 11,8
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.2 in 8
  have eq27 : sK0 ≠ sK0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq27 rfl


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
theorem Equation1318_implies_Equation114 (G : Type*) [Magma G] (h : Equation1318 G) : Equation114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation1328_implies_Equation2093 (G : Type*) [Magma G] (h : Equation1328 G) : Equation2093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1328_implies_Equation2173 (G : Type*) [Magma G] (h : Equation1328 G) : Equation2173 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1332_implies_Equation2107 (G : Type*) [Magma G] (h : Equation1332 G) : Equation2107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3) = (X0 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3) = (X0 ◇ X3) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq33 (X0 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = X3 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1334_implies_Equation1368 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1368 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.1.1 in 12
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq85 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) := superpose eq54 eq84 -- forward demodulation 84,54
  have eq86 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := superpose eq54 eq85 -- forward demodulation 85,54
  have eq87 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq113 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq87 -- superposition 87,62, 62 into 87, unify on (0).2 in 62 and (0).1.2 in 87
  have eq117 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq113 eq86 -- backward demodulation 86,113
  have eq118 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq70 eq117 -- forward demodulation 117,70
  subsumption eq118 eq62


@[equational_result]
theorem Equation1334_implies_Equation2308 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq121 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq56 eq49 -- superposition 49,56, 56 into 49, unify on (0).2 in 56 and (0).1 in 49
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq132 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) := superpose eq124 eq10 -- backward demodulation 10,124
  have eq133 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq84 eq132 -- forward demodulation 132,84
  subsumption eq133 eq121


@[equational_result]
theorem Equation1334_implies_Equation2789 (G : Type*) [Magma G] (h : Equation1334 G) : Equation2789 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X2 ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq64 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = (X2 ◇ X0) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq65 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) := superpose eq50 eq14 -- backward demodulation 14,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq71 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X4 ◇ (X2 ◇ (X0 ◇ X4))) := superpose eq50 eq65 -- forward demodulation 65,50
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = (X2 ◇ X0) := superpose eq70 eq71 -- forward demodulation 71,70
  have eq73 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK2) := superpose eq72 eq10 -- backward demodulation 10,72
  subsumption eq73 eq19


@[equational_result]
theorem Equation1334_implies_Equation3404 (G : Type*) [Magma G] (h : Equation1334 G) : Equation3404 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X4) ◇ X2) ◇ X4)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq12 eq21 -- forward demodulation 21,12
  have eq35 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X1)))) = X4 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq24 eq35 -- forward demodulation 35,24
  have eq50 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.1 in 19
  have eq55 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.2.2.1 in 11
  have eq56 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq9 -- backward demodulation 9,50
  have eq64 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq50 eq13 -- backward demodulation 13,50
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq50 eq64 -- forward demodulation 64,50
  have eq84 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq49 eq19 -- superposition 19,49, 49 into 19, unify on (0).2 in 49 and (0).1.1 in 19
  have eq133 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq62 eq84 -- superposition 84,62, 62 into 84, unify on (0).2 in 62 and (0).1.2 in 84
  have eq141 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq133 eq10 -- backward demodulation 10,133
  have eq142 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq124 eq141 -- forward demodulation 141,124
  subsumption eq142 eq70


@[equational_result]
theorem Equation1336_implies_Equation1405 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK3) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1340_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1171 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ X3) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4) ◇ X3)) ◇ X5) = (X1 ◇ X5) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq24 (X1 X3 X5 : G) : (X1 ◇ X5) = ((X3 ◇ (X1 ◇ X3)) ◇ X5) := superpose eq18 eq19 -- forward demodulation 19,18
  have eq30 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq30 eq17


@[equational_result]
theorem Equation1340_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1780 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq54 : sK0 ≠ sK0 := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq54 rfl


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
theorem Equation1351_implies_Equation472 (G : Type*) [Magma G] (h : Equation1351 G) : Equation472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq13 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq22 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq22 eq15


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
theorem Equation1358_implies_Equation1977 (G : Type*) [Magma G] (h : Equation1358 G) : Equation1977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq26 (X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq36 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X1 := superpose eq26 eq23 -- backward demodulation 23,26
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X4) ◇ X3) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X4) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq61 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.1.1 in 26
  have eq121 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq61 eq26 -- superposition 26,61, 61 into 26, unify on (0).2 in 61 and (0).1.1.1 in 26
  have eq128 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq61 eq36 -- superposition 36,61, 61 into 36, unify on (0).2 in 61 and (0).1.2.2.1 in 36
  have eq129 (X0 X1 X4 : G) : ((X4 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X4) = X0 := superpose eq128 eq46 -- backward demodulation 46,128
  have eq155 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X2 ◇ X3)) := superpose eq129 eq9 -- superposition 9,129, 129 into 9, unify on (0).2 in 129 and (0).1.2.1 in 9
  have eq237 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ X0)) ◇ (sK0 ◇ sK2)) := superpose eq155 eq10 -- superposition 10,155, 155 into 10, unify on (0).2 in 155 and (0).2.1 in 10
  subsumption eq237 eq121


@[equational_result]
theorem Equation1366_implies_Equation2178 (G : Type*) [Magma G] (h : Equation1366 G) : Equation2178 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ (X3 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq57 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1))) = (X0 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1)) ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1))))) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).1.1 in 19
  have eq59 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2 in 19
  have eq84 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq59 eq9 -- superposition 9,59, 59 into 9, unify on (0).2 in 59 and (0).1.2 in 9
  have eq97 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) = (X1 ◇ X3) := superpose eq84 eq12 -- backward demodulation 12,84
  have eq102 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1))) := superpose eq84 eq57 -- backward demodulation 57,84
  have eq130 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) ◇ X1) := superpose eq9 eq102 -- forward demodulation 102,9
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq97 eq130 -- forward demodulation 130,97
  have eq136 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq131 eq84 -- backward demodulation 84,131
  have eq138 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq131 eq9 -- backward demodulation 9,131
  have eq182 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq136 eq138 -- superposition 138,136, 136 into 138, unify on (0).2 in 136 and (0).1.2 in 138
  have eq183 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq136 eq182 -- forward demodulation 182,136
  have eq205 : sK0 ≠ sK0 := superpose eq183 eq10 -- superposition 10,183, 183 into 10, unify on (0).2 in 183 and (0).2 in 10
  subsumption eq205 rfl


@[equational_result]
theorem Equation1367_implies_Equation678 (G : Type*) [Magma G] (h : Equation1367 G) : Equation678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq20 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq22 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq13 eq11 -- backward demodulation 11,13
  have eq32 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) = X3 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.1 in 22
  have eq40 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X2) = X1 := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).1.2 in 9
  have eq51 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq40 eq20 -- backward demodulation 20,40
  have eq55 (X1 X3 X4 : G) : (X4 ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq22 eq51 -- superposition 51,22, 22 into 51, unify on (0).2 in 22 and (0).1 in 51
  have eq77 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK2))) := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2.2.2 in 10
  have eq101 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = X3 := superpose eq55 eq32 -- backward demodulation 32,55
  have eq104 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq40 eq101 -- forward demodulation 101,40
  subsumption eq77 eq104


@[equational_result]
theorem Equation1370_implies_Equation2203 (G : Type*) [Magma G] (h : Equation1370 G) : Equation2203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq20 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3)) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq25 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation1374_implies_Equation1340 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1340 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq27 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq27 eq22


@[equational_result]
theorem Equation1374_implies_Equation4200 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4200 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq95 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := superpose eq91 eq10 -- backward demodulation 10,91
  subsumption eq95 eq23


@[equational_result]
theorem Equation1374_implies_Equation4677 (G : Type*) [Magma G] (h : Equation1374 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq22 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq22 eq15 -- superposition 15,22, 22 into 15, unify on (0).2 in 22 and (0).1.2 in 15
  have eq247 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq91 eq10 -- superposition 10,91, 91 into 10, unify on (0).2 in 91 and (0).2 in 10
  subsumption eq247 rfl


@[equational_result]
theorem Equation1378_implies_Equation176 (G : Type*) [Magma G] (h : Equation1378 G) : Equation176 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : (X1 ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


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
theorem Equation1405_implies_Equation138 (G : Type*) [Magma G] (h : Equation1405 G) : Equation138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1405_implies_Equation2161 (G : Type*) [Magma G] (h : Equation1405 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 (X1 X4 X5 : G) : ((X1 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation1405_implies_Equation4040 (G : Type*) [Magma G] (h : Equation1405 G) : Equation4040 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X4) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ X3) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq106 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq106 rfl


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
theorem Equation1433_implies_Equation2261 (G : Type*) [Magma G] (h : Equation1433 G) : Equation2261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1433_implies_Equation2285 (G : Type*) [Magma G] (h : Equation1433 G) : Equation2285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


@[equational_result]
theorem Equation1436_implies_Equation2478 (G : Type*) [Magma G] (h : Equation1436 G) : Equation2478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1438_implies_Equation1436 (G : Type*) [Magma G] (h : Equation1438 G) : Equation1436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation1439_implies_Equation2478 (G : Type*) [Magma G] (h : Equation1439 G) : Equation2478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq21 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq21 eq13


@[equational_result]
theorem Equation1440_implies_Equation1856 (G : Type*) [Magma G] (h : Equation1440 G) : Equation1856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X4) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X4 : G) : ((X4 ◇ X4) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation1444_implies_Equation4065 (G : Type*) [Magma G] (h : Equation1444 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation1446_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq138 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq138 rfl


@[equational_result]
theorem Equation1446_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq77 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation1446_implies_Equation1868 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1447_implies_Equation4067 (G : Type*) [Magma G] (h : Equation1447 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1448_implies_Equation1869 (G : Type*) [Magma G] (h : Equation1448 G) : Equation1869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq138 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq153 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq138 eq138 -- superposition 138,138, 138 into 138, unify on (0).2 in 138 and (0).1.1 in 138
  have eq433 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq153 eq9 -- superposition 9,153, 153 into 9, unify on (0).2 in 153 and (0).1.2 in 9
  have eq499 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq13 eq80 -- superposition 80,13, 13 into 80, unify on (0).2 in 13 and (0).2.2 in 80
  have eq537 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq433 eq499 -- forward demodulation 499,433
  have eq567 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq537 eq25 -- superposition 25,537, 537 into 25, unify on (0).2 in 537 and (0).1.1.2 in 25
  have eq1674 : sK0 ≠ sK0 := superpose eq567 eq10 -- superposition 10,567, 567 into 10, unify on (0).2 in 567 and (0).2 in 10
  subsumption eq1674 rfl


@[equational_result]
theorem Equation1449_implies_Equation158 (G : Type*) [Magma G] (h : Equation1449 G) : Equation158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1456_implies_Equation2270 (G : Type*) [Magma G] (h : Equation1456 G) : Equation2270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq49 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1460_implies_Equation3527 (G : Type*) [Magma G] (h : Equation1460 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq48 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 rfl


@[equational_result]
theorem Equation1461_implies_Equation1447 (G : Type*) [Magma G] (h : Equation1461 G) : Equation1447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq25 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq9


@[equational_result]
theorem Equation1461_implies_Equation4134 (G : Type*) [Magma G] (h : Equation1461 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq248 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq33 -- superposition 33,9, 9 into 33, unify on (0).2 in 9 and (0).2.2.2 in 33
  have eq376 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq248 -- superposition 248,12, 12 into 248, unify on (0).2 in 12 and (0).2.2 in 248
  have eq409 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq376 -- forward demodulation 376,9
  have eq902 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq409 eq9 -- superposition 9,409, 409 into 9, unify on (0).2 in 409 and (0).1.2 in 9
  have eq1153 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq902 eq10 -- superposition 10,902, 902 into 10, unify on (0).2 in 902 and (0).2 in 10
  subsumption eq1153 rfl


@[equational_result]
theorem Equation1461_implies_Equation4316 (G : Type*) [Magma G] (h : Equation1461 G) : Equation4316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq25 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq25 eq20


@[equational_result]
theorem Equation1465_implies_Equation1473 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1465_implies_Equation4360 (G : Type*) [Magma G] (h : Equation1465 G) : Equation4360 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ X0)) := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2.2.2 in 11
  have eq141 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (X0 ◇ sK2)) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq141 eq47


@[equational_result]
theorem Equation1466_implies_Equation1468 (G : Type*) [Magma G] (h : Equation1466 G) : Equation1468 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ X2)) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq37 eq14


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
theorem Equation1468_implies_Equation1842 (G : Type*) [Magma G] (h : Equation1468 G) : Equation1842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X2 X4 : G) : ((X4 ◇ X2) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation1470_implies_Equation1670 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq52 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  have eq69 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq76 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq69 eq13 -- backward demodulation 13,69
  subsumption eq52 eq76


@[equational_result]
theorem Equation1470_implies_Equation1873 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq99 : sK0 ≠ sK0 := superpose eq75 eq10 -- superposition 10,75, 75 into 10, unify on (0).2 in 75 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation1483_implies_Equation2163 (G : Type*) [Magma G] (h : Equation1483 G) : Equation2163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


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
theorem Equation1485_implies_Equation2162 (G : Type*) [Magma G] (h : Equation1485 G) : Equation2162 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1.2 in 12
  have eq50 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation1487_implies_Equation2089 (G : Type*) [Magma G] (h : Equation1487 G) : Equation2089 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X1)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1487_implies_Equation2163 (G : Type*) [Magma G] (h : Equation1487 G) : Equation2163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X1)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1487_implies_Equation2164 (G : Type*) [Magma G] (h : Equation1487 G) : Equation2164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X5 ◇ X1)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1489_implies_Equation255 (G : Type*) [Magma G] (h : Equation1489 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation1490_implies_Equation874 (G : Type*) [Magma G] (h : Equation1490 G) : Equation874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1 in 12
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X2)) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1.1 in 13
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq13 eq21 -- superposition 21,13, 13 into 21, unify on (0).2 in 13 and (0).1.1 in 21
  have eq75 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ (X0 ◇ X2))) = X4 := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1.2 in 21
  have eq78 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X2)) := superpose eq75 eq29 -- backward demodulation 29,75
  have eq79 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq75 eq26 -- backward demodulation 26,75
  have eq81 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK2))) := superpose eq78 eq10 -- backward demodulation 10,78
  have eq83 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := superpose eq78 eq81 -- forward demodulation 81,78
  have eq84 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq21 eq79 -- forward demodulation 79,21
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq84 eq9 -- backward demodulation 9,84
  have eq87 (X0 X1 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq84 eq12 -- backward demodulation 12,84
  have eq113 : sK0 ≠ (sK1 ◇ sK2) := superpose eq84 eq83 -- backward demodulation 83,84
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq85 eq35 -- backward demodulation 35,85
  have eq120 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq84 eq87 -- forward demodulation 87,84
  have eq124 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq120 eq114 -- backward demodulation 114,120
  subsumption eq113 eq124


@[equational_result]
theorem Equation1491_implies_Equation359 (G : Type*) [Magma G] (h : Equation1491 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq65 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq65 rfl


@[equational_result]
theorem Equation1491_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1491 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq60 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).1 in 15
  have eq65 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq14 eq60 -- forward demodulation 60,14
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq10 eq65 -- forward demodulation 65,10
  have eq137 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq66 eq9 -- superposition 9,66, 66 into 9, unify on (0).2 in 66 and (0).2 in 9
  subsumption eq137 rfl


@[equational_result]
theorem Equation1491_implies_Equation47 (G : Type*) [Magma G] (h : Equation1491 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq80 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.2.2.1 in 12
  have eq93 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq80 -- forward demodulation 80,12
  have eq94 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq14 eq93 -- forward demodulation 93,14
  have eq95 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq94 -- forward demodulation 94,10
  have eq98 : sK0 ≠ sK0 := superpose eq95 eq9 -- superposition 9,95, 95 into 9, unify on (0).2 in 95 and (0).2 in 9
  subsumption eq98 rfl


@[equational_result]
theorem Equation1491_implies_Equation614 (G : Type*) [Magma G] (h : Equation1491 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq33 eq13 -- superposition 13,33, 33 into 13, unify on (0).2 in 33 and (0).1.2.2.1 in 13
  have eq105 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq91 -- forward demodulation 91,13
  have eq106 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq15 eq105 -- forward demodulation 105,15
  have eq107 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq11 -- superposition 11,107, 107 into 11, unify on (0).2 in 107 and (0).2 in 11
  subsumption eq117 rfl


@[equational_result]
theorem Equation1491_implies_Equation817 (G : Type*) [Magma G] (h : Equation1491 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2 in 10
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1.2 in 10
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq63 -- forward demodulation 63,10
  have eq70 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq68 eq9 -- backward demodulation 9,68
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.2.2.1 in 12
  have eq105 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq91 -- forward demodulation 91,12
  have eq106 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq14 eq105 -- forward demodulation 105,14
  have eq107 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq122 : sK0 ≠ sK0 := superpose eq107 eq70 -- superposition 70,107, 107 into 70, unify on (0).2 in 107 and (0).2 in 70
  subsumption eq122 rfl


@[equational_result]
theorem Equation1494_implies_Equation761 (G : Type*) [Magma G] (h : Equation1494 G) : Equation761 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq38 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := superpose eq27 eq10 -- backward demodulation 10,27
  have eq39 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq27 eq38 -- forward demodulation 38,27
  have eq42 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = (X1 ◇ ((X2 ◇ X1) ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1))))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.1 in 11
  have eq53 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = (X4 ◇ ((X0 ◇ X4) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.2 in 11
  have eq65 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = (X2 ◇ (X3 ◇ X1)) := superpose eq53 eq42 -- backward demodulation 42,53
  have eq73 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).1 in 27
  have eq79 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq27 eq27 -- superposition 27,27, 27 into 27, unify on (0).2 in 27 and (0).2.2.1 in 27
  have eq114 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq27 eq39 -- superposition 39,27, 27 into 39, unify on (0).2 in 27 and (0).2.2 in 39
  have eq116 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq73 eq79 -- forward demodulation 79,73
  have eq167 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ sK0))) := superpose eq27 eq114 -- superposition 114,27, 27 into 114, unify on (0).2 in 27 and (0).2.2 in 114
  have eq272 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = ((X0 ◇ X1) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq65 eq27 -- superposition 27,65, 65 into 27, unify on (0).2 in 65 and (0).2.2 in 27
  have eq306 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq9 eq272 -- forward demodulation 272,9
  have eq307 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq306 eq116 -- backward demodulation 116,306
  have eq438 : sK0 ≠ sK0 := superpose eq307 eq167 -- superposition 167,307, 307 into 167, unify on (0).2 in 307 and (0).2 in 167
  subsumption eq438 rfl


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
theorem Equation1499_implies_Equation3181 (G : Type*) [Magma G] (h : Equation1499 G) : Equation3181 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X1 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq17 eq11 -- backward demodulation 11,17
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq17 eq23 -- forward demodulation 23,17
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := superpose eq17 eq25 -- forward demodulation 25,17
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq18 eq26 -- backward demodulation 26,18
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq27 eq13 -- backward demodulation 13,27
  have eq33 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq27 eq29 -- forward demodulation 29,27
  have eq37 : sK0 ≠ sK0 := superpose eq33 eq14 -- superposition 14,33, 33 into 14, unify on (0).2 in 33 and (0).2 in 14
  subsumption eq37 rfl


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
theorem Equation1502_implies_Equation90 (G : Type*) [Magma G] (h : Equation1502 G) : Equation90 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X5 ◇ (X1 ◇ X2))) = (X4 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq28 (X0 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  have eq32 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X3 ◇ X2))) = X2 := superpose eq9 eq14 -- forward demodulation 14,9
  subsumption eq28 eq32


@[equational_result]
theorem Equation1506_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1506 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq27 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).1.2 in 9
  have eq85 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ X0)) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq125 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq32 eq85 -- superposition 85,32, 32 into 85, unify on (0).2 in 32 and (0).1 in 85
  have eq365 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq125 eq9 -- superposition 9,125, 125 into 9, unify on (0).2 in 125 and (0).1.1 in 9
  have eq368 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq125 eq85 -- superposition 85,125, 125 into 85, unify on (0).2 in 125 and (0).1.2 in 85
  have eq378 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq368 eq365 -- backward demodulation 365,368
  have eq918 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq378 eq34 -- superposition 34,378, 378 into 34, unify on (0).2 in 378 and (0).2.1 in 34
  have eq1548 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq918 eq10 -- superposition 10,918, 918 into 10, unify on (0).2 in 918 and (0).2 in 10
  subsumption eq1548 rfl


@[equational_result]
theorem Equation1510_implies_Equation748 (G : Type*) [Magma G] (h : Equation1510 G) : Equation748 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq13 (X1 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X3 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq21 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq43 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.2 in 21
  subsumption eq43 eq28


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
theorem Equation1521_implies_Equation1564 (G : Type*) [Magma G] (h : Equation1521 G) : Equation1564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq81 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq115 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq134 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) = X2 := superpose eq81 eq9 -- superposition 9,81, 81 into 9, unify on (0).2 in 81 and (0).1.1 in 9
  have eq150 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose eq81 eq115 -- superposition 115,81, 81 into 115, unify on (0).2 in 81 and (0).2.2.2 in 115
  subsumption eq150 eq134


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
theorem Equation1526_implies_Equation2644 (G : Type*) [Magma G] (h : Equation1526 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1531_implies_Equation78 (G : Type*) [Magma G] (h : Equation1531 G) : Equation78 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X3) ◇ (X3 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X5) ◇ (X5 ◇ (X0 ◇ X1))) = (X4 ◇ (X2 ◇ (X3 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq37 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X3 ◇ X1))) = X1 := superpose eq9 eq15 -- forward demodulation 15,9
  have eq55 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq110 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ sK0))) := superpose eq55 eq10 -- superposition 10,55, 55 into 10, unify on (0).2 in 55 and (0).2.2 in 10
  subsumption eq110 eq37


@[equational_result]
theorem Equation1535_implies_Equation1608 (G : Type*) [Magma G] (h : Equation1535 G) : Equation1608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK0))) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq21 eq11


@[equational_result]
theorem Equation1536_implies_Equation3025 (G : Type*) [Magma G] (h : Equation1536 G) : Equation3025 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation1539_implies_Equation897 (G : Type*) [Magma G] (h : Equation1539 G) : Equation897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq24 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ (sK2 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq24 eq18


@[equational_result]
theorem Equation154_implies_Equation2261 (G : Type*) [Magma G] (h : Equation154 G) : Equation2261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq12


@[equational_result]
theorem Equation1547_implies_Equation791 (G : Type*) [Magma G] (h : Equation1547 G) : Equation791 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1552_implies_Equation1521 (G : Type*) [Magma G] (h : Equation1552 G) : Equation1521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq27 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq37 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq27 -- forward demodulation 27,9
  have eq45 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).1 in 37
  have eq118 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).1.2.2 in 11
  have eq126 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := superpose eq45 eq10 -- superposition 10,45, 45 into 10, unify on (0).2 in 45 and (0).2 in 10
  subsumption eq126 eq118


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
theorem Equation1556_implies_Equation1494 (G : Type*) [Magma G] (h : Equation1556 G) : Equation1494 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq27 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq65 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  have eq149 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq20 eq27 -- superposition 27,20, 20 into 27, unify on (0).2 in 20 and (0).1.2 in 27
  have eq252 (X0 X1 : G) : sK0 ≠ (X1 ◇ (sK1 ◇ (X0 ◇ sK0))) := superpose eq20 eq65 -- superposition 65,20, 20 into 65, unify on (0).2 in 20 and (0).2.2.2 in 65
  subsumption eq252 eq149


@[equational_result]
theorem Equation1556_implies_Equation1623 (G : Type*) [Magma G] (h : Equation1556 G) : Equation1623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK4 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq27 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq65 (X0 : G) : sK0 ≠ (X0 ◇ (sK3 ◇ (sK4 ◇ sK0))) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  have eq149 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq20 eq27 -- superposition 27,20, 20 into 27, unify on (0).2 in 20 and (0).1.2 in 27
  have eq252 (X0 X1 : G) : sK0 ≠ (X1 ◇ (sK3 ◇ (X0 ◇ sK0))) := superpose eq20 eq65 -- superposition 65,20, 20 into 65, unify on (0).2 in 20 and (0).2.2.2 in 65
  subsumption eq252 eq149


@[equational_result]
theorem Equation1556_implies_Equation889 (G : Type*) [Magma G] (h : Equation1556 G) : Equation889 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2 in 13
  have eq27 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X2 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq65 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.2 in 10
  have eq260 : sK0 ≠ sK0 := superpose eq27 eq65 -- superposition 65,27, 27 into 65, unify on (0).2 in 27 and (0).2 in 65
  subsumption eq260 rfl


@[equational_result]
theorem Equation1560_implies_Equation653 (G : Type*) [Magma G] (h : Equation1560 G) : Equation653 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq87 -- forward demodulation 87,9
  have eq95 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq80 eq12 -- superposition 12,80, 80 into 12, unify on (0).2 in 80 and (0).1.2 in 12
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq95 eq143 -- forward demodulation 143,95
  have eq153 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq144 eq22 -- backward demodulation 22,144
  have eq166 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X3 := superpose eq153 eq11 -- backward demodulation 11,153
  have eq194 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq166 -- superposition 166,16, 16 into 166, unify on (0).2 in 16 and (0).1.2.2 in 166
  have eq203 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq194 eq10 -- backward demodulation 10,194
  subsumption eq203 eq80


@[equational_result]
theorem Equation1560_implies_Equation960 (G : Type*) [Magma G] (h : Equation1560 G) : Equation960 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq87 -- forward demodulation 87,9
  have eq95 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq80 eq12 -- superposition 12,80, 80 into 12, unify on (0).2 in 80 and (0).1.2 in 12
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq95 eq143 -- forward demodulation 143,95
  have eq153 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq144 eq22 -- backward demodulation 22,144
  have eq169 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X3 := superpose eq153 eq11 -- backward demodulation 11,153
  have eq203 : sK0 ≠ sK0 := superpose eq169 eq10 -- superposition 10,169, 169 into 10, unify on (0).2 in 169 and (0).2 in 10
  subsumption eq203 rfl


@[equational_result]
theorem Equation1569_implies_Equation78 (G : Type*) [Magma G] (h : Equation1569 G) : Equation78 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq18 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq23 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq23 eq14


@[equational_result]
theorem Equation1571_implies_Equation1334 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq46 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1 in 9
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq53 eq38 -- superposition 38,53, 53 into 38, unify on (0).2 in 53 and (0).1.2 in 38
  have eq85 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := superpose eq72 eq10 -- backward demodulation 10,72
  have eq86 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq72 eq85 -- forward demodulation 85,72
  subsumption eq86 eq46


@[equational_result]
theorem Equation1571_implies_Equation546 (G : Type*) [Magma G] (h : Equation1571 G) : Equation546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq32 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq38 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X0 := superpose eq9 eq32 -- forward demodulation 32,9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq9 eq38 -- superposition 38,9, 9 into 38, unify on (0).2 in 9 and (0).1.2 in 38
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq39 eq15 -- backward demodulation 15,39
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq52 eq13 -- backward demodulation 13,52
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = (X0 ◇ X1) := superpose eq9 eq53 -- superposition 53,9, 9 into 53, unify on (0).2 in 9 and (0).1.1 in 53
  have eq78 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq65 eq10 -- backward demodulation 10,65
  subsumption eq78 eq38


@[equational_result]
theorem Equation157_implies_Equation1882 (G : Type*) [Magma G] (h : Equation157 G) : Equation1882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK3 ◇ sK3)) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2 in 12
  subsumption eq16 eq9


@[equational_result]
theorem Equation157_implies_Equation3087 (G : Type*) [Magma G] (h : Equation157 G) : Equation3087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq19 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq13 eq12 -- backward demodulation 12,13
  subsumption eq19 eq13


@[equational_result]
theorem Equation1573_implies_Equation806 (G : Type*) [Magma G] (h : Equation1573 G) : Equation806 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq21 : sK0 ≠ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq21 eq13


@[equational_result]
theorem Equation1581_implies_Equation985 (G : Type*) [Magma G] (h : Equation1581 G) : Equation985 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation1586_implies_Equation4689 (G : Type*) [Magma G] (h : Equation1586 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1.2 in 11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq82 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X0 := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.2 in 21
  have eq503 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq14 eq12 -- superposition 12,14, 14 into 12, unify on (0).2 in 14 and (0).2.2 in 12
  have eq557 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X5))) = X5 := superpose eq9 eq82 -- superposition 82,9, 9 into 82, unify on (0).2 in 9 and (0).1.2.1 in 82
  have eq695 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = (X0 ◇ X2) := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).2.2 in 17
  have eq797 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ X2) := superpose eq695 eq503 -- backward demodulation 503,695
  have eq1111 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)))) ◇ X4) := superpose eq17 eq797 -- superposition 797,17, 17 into 797, unify on (0).2 in 17 and (0).1.1.2.1 in 797
  have eq1228 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X3 ◇ X0) ◇ X4) := superpose eq557 eq1111 -- forward demodulation 1111,557
  have eq1626 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X1) := superpose eq1228 eq1228 -- superposition 1228,1228, 1228 into 1228, unify on (0).2 in 1228 and (0).1 in 1228
  have eq1793 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq1228 eq10 -- superposition 10,1228, 1228 into 10, unify on (0).2 in 1228 and (0).2 in 10
  subsumption eq1793 eq1626


@[equational_result]
theorem Equation1594_implies_Equation4689 (G : Type*) [Magma G] (h : Equation1594 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq31 eq9 -- superposition 9,31, 31 into 9, unify on (0).2 in 31 and (0).1.2 in 9
  have eq294 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq294 eq46


@[equational_result]
theorem Equation1594_implies_Equation619 (G : Type*) [Magma G] (h : Equation1594 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq45 rfl


@[equational_result]
theorem Equation1594_implies_Equation727 (G : Type*) [Magma G] (h : Equation1594 G) : Equation727 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq51 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq51 rfl


@[equational_result]
theorem Equation1594_implies_Equation882 (G : Type*) [Magma G] (h : Equation1594 G) : Equation882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq20 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) = X3 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq64 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq20 eq31 -- superposition 31,20, 20 into 31, unify on (0).2 in 20 and (0).1.2 in 31
  have eq76 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X3 := superpose eq64 eq20 -- backward demodulation 20,64
  have eq109 : sK0 ≠ sK0 := superpose eq76 eq10 -- superposition 10,76, 76 into 10, unify on (0).2 in 76 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation1598_implies_Equation752 (G : Type*) [Magma G] (h : Equation1598 G) : Equation752 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X3 X4 X5 : G) : (X4 ◇ X5) = (X3 ◇ X5) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq47 (X2 X3 X4 X5 : G) : (X2 ◇ (X5 ◇ (X3 ◇ X4))) = X4 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq81 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.2.2 in 10
  subsumption eq81 eq47


@[equational_result]
theorem Equation160_implies_Equation203 (G : Type*) [Magma G] (h : Equation160 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation160_implies_Equation212 (G : Type*) [Magma G] (h : Equation160 G) : Equation212 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1608_implies_Equation922 (G : Type*) [Magma G] (h : Equation1608 G) : Equation922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X2 ◇ X4) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq26 eq20


@[equational_result]
theorem Equation1613_implies_Equation951 (G : Type*) [Magma G] (h : Equation1613 G) : Equation951 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X1 ◇ X3))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq26 eq20


@[equational_result]
theorem Equation1618_implies_Equation1547 (G : Type*) [Magma G] (h : Equation1618 G) : Equation1547 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X4 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq67 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq73 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq73 eq67


@[equational_result]
theorem Equation1623_implies_Equation994 (G : Type*) [Magma G] (h : Equation1623 G) : Equation994 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X4 X5 X6 X7 : G) : (X4 ◇ (X5 ◇ (X6 ◇ X7))) = X7 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1636_implies_Equation1633 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = ((((X3 ◇ (X0 ◇ X0)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).1.1 in 21
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq14 eq341 -- superposition 341,14, 14 into 341, unify on (0).2 in 14 and (0).2.2 in 341
  have eq451 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq378 eq138 -- backward demodulation 138,378
  have eq551 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq451 eq9 -- superposition 9,451, 451 into 9, unify on (0).2 in 451 and (0).1.2.1 in 9
  have eq949 : sK0 ≠ sK0 := superpose eq551 eq10 -- superposition 10,551, 551 into 10, unify on (0).2 in 551 and (0).2 in 10
  subsumption eq949 rfl


@[equational_result]
theorem Equation1636_implies_Equation1839 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq14


@[equational_result]
theorem Equation1636_implies_Equation1849 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq377 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := superpose eq341 eq10 -- backward demodulation 10,341
  subsumption eq377 eq14


@[equational_result]
theorem Equation1636_implies_Equation2249 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  subsumption eq56 eq12


@[equational_result]
theorem Equation1636_implies_Equation2452 (G : Type*) [Magma G] (h : Equation1636 G) : Equation2452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq268 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2.2.1 in 35
  have eq312 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq268 eq10 -- backward demodulation 10,268
  subsumption eq312 eq12


@[equational_result]
theorem Equation1636_implies_Equation308 (G : Type*) [Magma G] (h : Equation1636 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq116 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq116 rfl


@[equational_result]
theorem Equation1636_implies_Equation3460 (G : Type*) [Magma G] (h : Equation1636 G) : Equation3460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq268 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq35 -- superposition 35,16, 16 into 35, unify on (0).2 in 16 and (0).2.2.1 in 35
  have eq643 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq268 eq10 -- superposition 10,268, 268 into 10, unify on (0).2 in 268 and (0).2 in 10
  subsumption eq643 rfl


@[equational_result]
theorem Equation1636_implies_Equation4127 (G : Type*) [Magma G] (h : Equation1636 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X4) = ((((X3 ◇ (X0 ◇ X0)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq21 -- superposition 21,14, 14 into 21, unify on (0).2 in 14 and (0).1.1 in 21
  have eq341 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq74 -- superposition 74,16, 16 into 74, unify on (0).2 in 16 and (0).2.2 in 74
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq341 -- superposition 341,14, 14 into 341, unify on (0).2 in 14 and (0).2.2 in 341
  have eq451 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq378 eq138 -- backward demodulation 138,378
  have eq551 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq451 eq10 -- superposition 10,451, 451 into 10, unify on (0).2 in 451 and (0).2 in 10
  subsumption eq551 rfl


@[equational_result]
theorem Equation1636_implies_Equation4286 (G : Type*) [Magma G] (h : Equation1636 G) : Equation4286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq56 : (sK0 ◇ (sK2 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq44 eq10 -- backward demodulation 10,44
  have eq63 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).2.1 in 15
  have eq387 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq63 -- superposition 63,16, 16 into 63, unify on (0).2 in 16 and (0).2.2 in 63
  have eq479 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq387 eq56 -- superposition 56,387, 387 into 56, unify on (0).2 in 387 and (0).1 in 56
  subsumption eq479 rfl


@[equational_result]
theorem Equation1641_implies_Equation1435 (G : Type*) [Magma G] (h : Equation1641 G) : Equation1435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation1642_implies_Equation1859 (G : Type*) [Magma G] (h : Equation1642 G) : Equation1859 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1 in 18
  have eq32 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq33 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq24 eq32 -- forward demodulation 32,24
  subsumption eq33 eq18


@[equational_result]
theorem Equation1645_implies_Equation2441 (G : Type*) [Magma G] (h : Equation1645 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


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
theorem Equation1651_implies_Equation1878 (G : Type*) [Magma G] (h : Equation1651 G) : Equation1878 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).2.1 in 12
  have eq35 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq12 -- superposition 12,16, 16 into 12, unify on (0).2 in 16 and (0).2.1 in 12
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq35 eq25 -- backward demodulation 25,35
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq43 eq24 -- backward demodulation 24,43
  have eq48 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK3)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq49 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK3)) := superpose eq35 eq48 -- forward demodulation 48,35
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2 in 45
  have eq108 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).1 in 51
  have eq138 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq51 eq49 -- superposition 49,51, 51 into 49, unify on (0).2 in 51 and (0).2 in 49
  subsumption eq138 eq108


@[equational_result]
theorem Equation1652_implies_Equation2464 (G : Type*) [Magma G] (h : Equation1652 G) : Equation2464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.1 in 11
  have eq30 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq31 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq30 -- forward demodulation 30,14
  have eq88 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).2 in 23
  have eq181 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq13 eq88 -- superposition 88,13, 13 into 88, unify on (0).2 in 13 and (0).1 in 88
  have eq222 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ X0) := superpose eq88 eq31 -- superposition 31,88, 88 into 31, unify on (0).2 in 88 and (0).2 in 31
  subsumption eq222 eq181


@[equational_result]
theorem Equation1656_implies_Equation1852 (G : Type*) [Magma G] (h : Equation1656 G) : Equation1852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1 in 9
  have eq98 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq98 rfl


@[equational_result]
theorem Equation1656_implies_Equation3527 (G : Type*) [Magma G] (h : Equation1656 G) : Equation3527 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2.2.1 in 14
  have eq162 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq36 -- superposition 36,9, 9 into 36, unify on (0).2 in 9 and (0).2.2 in 36
  have eq227 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq227 eq162


@[equational_result]
theorem Equation1659_implies_Equation2473 (G : Type*) [Magma G] (h : Equation1659 G) : Equation2473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq19 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq13


@[equational_result]
theorem Equation1661_implies_Equation2481 (G : Type*) [Magma G] (h : Equation1661 G) : Equation2481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq22 eq18 -- backward demodulation 18,22
  have eq38 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq38 eq35


