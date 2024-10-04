import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation50_implies_Equation3659 (G : Type*) [Magma G] (h : Equation50 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1243_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1243 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq36 : sK0 ≠ sK0 := superpose eq27 eq10 -- superposition 10,27, 27 into 10, unify on (0).2 in 27 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation1050_implies_Equation56 (G : Type*) [Magma G] (h : Equation1050 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation847_implies_Equation99 (G : Type*) [Magma G] (h : Equation847 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation847_implies_Equation108 (G : Type*) [Magma G] (h : Equation847 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation362_implies_Equation4068 (G : Type*) [Magma G] (h : Equation362 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ X0) ◇ X0) ◇ sK0) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq41 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq9 eq35 -- forward demodulation 35,9
  subsumption eq41 eq9


@[equational_result]
theorem Equation315_implies_Equation3278 (G : Type*) [Magma G] (h : Equation315 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq55 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.2 in 30
  have eq63 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq9 eq55 -- forward demodulation 55,9
  subsumption eq63 eq9


@[equational_result]
theorem Equation3671_implies_Equation3662 (G : Type*) [Magma G] (h : Equation3671 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq63 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1 in 16
  have eq93 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq63 -- forward demodulation 63,9
  have eq115 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation2688_implies_Equation4656 (G : Type*) [Magma G] (h : Equation2688 G) : Equation4656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq54 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X3)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq59 (X0 X1 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X1) ◇ X1) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq109 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose eq54 eq59 -- superposition 59,54, 54 into 59, unify on (0).2 in 54 and (0).1.1.1 in 59
  have eq186 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ X0) ◇ X0) := superpose eq109 eq10 -- superposition 10,109, 109 into 10, unify on (0).2 in 109 and (0).2 in 10
  subsumption eq186 eq109


@[equational_result]
theorem Equation2688_implies_Equation4341 (G : Type*) [Magma G] (h : Equation2688 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq27 eq12


@[equational_result]
theorem Equation1641_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1641 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


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
theorem Equation1245_implies_Equation1249 (G : Type*) [Magma G] (h : Equation1245 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq28 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq55 (X0 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).1.2.1.1.1 in 28
  have eq83 : sK0 ≠ sK0 := superpose eq55 eq10 -- superposition 10,55, 55 into 10, unify on (0).2 in 55 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation1052_implies_Equation817 (G : Type*) [Magma G] (h : Equation1052 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.2 in 8
  have eq18 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.1 in 8
  have eq41 : sK0 ≠ sK0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq41 rfl


@[equational_result]
theorem Equation1052_implies_Equation846 (G : Type*) [Magma G] (h : Equation1052 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq49 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation1052_implies_Equation108 (G : Type*) [Magma G] (h : Equation1052 G) : Equation108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation646_implies_Equation56 (G : Type*) [Magma G] (h : Equation646 G) : Equation56 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation4100_implies_Equation359 (G : Type*) [Magma G] (h : Equation4100 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X2) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation3973_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3973 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1 in 21
  have eq60 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2))) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq192 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq56 eq56 -- superposition 56,56, 56 into 56, unify on (0).2 in 56 and (0).1.1 in 56
  have eq309 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X3))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq357 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ (((X4 ◇ X3) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq192 eq309 -- forward demodulation 309,192
  have eq358 (X0 X2 X4 : G) : (X4 ◇ X0) = (X2 ◇ (X2 ◇ (X4 ◇ X0))) := superpose eq60 eq357 -- forward demodulation 357,60
  have eq422 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq358 eq10 -- superposition 10,358, 358 into 10, unify on (0).2 in 358 and (0).2 in 10
  subsumption eq422 rfl


@[equational_result]
theorem Equation3973_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3973 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1 in 21
  have eq60 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2))) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq192 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq56 eq56 -- superposition 56,56, 56 into 56, unify on (0).2 in 56 and (0).1.1 in 56
  have eq309 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X3))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq357 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ (((X4 ◇ X3) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq192 eq309 -- forward demodulation 309,192
  have eq358 (X0 X2 X4 : G) : (X4 ◇ X0) = (X2 ◇ (X2 ◇ (X4 ◇ X0))) := superpose eq60 eq357 -- forward demodulation 357,60
  have eq422 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq358 eq10 -- superposition 10,358, 358 into 10, unify on (0).2 in 358 and (0).2 in 10
  subsumption eq422 rfl


@[equational_result]
theorem Equation3973_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3973 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1 in 21
  have eq60 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2))) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq192 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq56 eq56 -- superposition 56,56, 56 into 56, unify on (0).2 in 56 and (0).1.1 in 56
  have eq309 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X3))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq357 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ (((X4 ◇ X3) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq192 eq309 -- forward demodulation 309,192
  have eq358 (X0 X2 X4 : G) : (X4 ◇ X0) = (X2 ◇ (X2 ◇ (X4 ◇ X0))) := superpose eq60 eq357 -- forward demodulation 357,60
  have eq422 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq358 eq10 -- superposition 10,358, 358 into 10, unify on (0).2 in 358 and (0).2 in 10
  subsumption eq422 rfl


@[equational_result]
theorem Equation3698_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3698 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq66 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq93 (X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq66 -- forward demodulation 66,9
  have eq115 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation3284_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3284 G) : Equation3268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq40 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq20 -- forward demodulation 20,16
  have eq128 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2 in 10
  subsumption eq128 eq40


@[equational_result]
theorem Equation3284_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3284 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq40 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq20 -- forward demodulation 20,16
  have eq128 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2 in 10
  subsumption eq128 eq40


@[equational_result]
theorem Equation3284_implies_Equation4351 (G : Type*) [Magma G] (h : Equation3284 G) : Equation4351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq21 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq128 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (X0 ◇ (sK1 ◇ sK1)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq128 eq21


@[equational_result]
theorem Equation3284_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3284 G) : Equation3288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq20 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq40 (X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq16 eq20 -- forward demodulation 20,16
  have eq128 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2 in 10
  subsumption eq128 eq40


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
theorem Equation2778_implies_Equation221 (G : Type*) [Magma G] (h : Equation2778 G) : Equation221 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2778_implies_Equation211 (G : Type*) [Magma G] (h : Equation2778 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (((X3 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X2) = (((X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X3 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq72 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1 in 14
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1 in 11
  have eq239 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq73 eq23 -- superposition 23,73, 73 into 23, unify on (0).2 in 73 and (0).2.1 in 23
  have eq713 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq72 eq239 -- superposition 239,72, 72 into 239, unify on (0).2 in 72 and (0).2.1 in 239
  have eq3266 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq713 eq9 -- superposition 9,713, 713 into 9, unify on (0).2 in 713 and (0).1.1 in 9
  have eq3597 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq3266 eq9 -- superposition 9,3266, 3266 into 9, unify on (0).2 in 3266 and (0).1.1 in 9
  have eq3888 : sK0 ≠ sK0 := superpose eq3597 eq10 -- superposition 10,3597, 3597 into 10, unify on (0).2 in 3597 and (0).2 in 10
  subsumption eq3888 rfl


@[equational_result]
theorem Equation2687_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2687 G) : Equation2662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X0) = (((((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X0 ◇ X0)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq168 (X0 X3 X4 X5 : G) : (X0 ◇ X0) = ((((X0 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X0 ◇ X0)) := superpose eq20 eq42 -- superposition 42,20, 20 into 42, unify on (0).2 in 20 and (0).2.1.1.1 in 42
  have eq173 (X0 X1 X3 X4 X5 X6 : G) : (X0 ◇ X0) = (((((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)) ◇ (X0 ◇ X0)) := superpose eq11 eq42 -- superposition 42,11, 11 into 42, unify on (0).2 in 11 and (0).2.1.1.1 in 42
  have eq536 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ X0) = (((((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)) ◇ (X0 ◇ X0)) := superpose eq19 eq173 -- superposition 173,19, 19 into 173, unify on (0).2 in 19 and (0).2.1.1.1.1 in 173
  have eq5798 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq168 eq536 -- superposition 536,168, 168 into 536, unify on (0).2 in 168 and (0).2.1 in 536
  have eq6105 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq5798 -- superposition 5798,9, 9 into 5798, unify on (0).2 in 9 and (0).2.1.1 in 5798
  have eq6494 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq6105 eq9 -- superposition 9,6105, 6105 into 9, unify on (0).2 in 6105 and (0).1.1 in 9
  have eq6860 : sK0 ≠ sK0 := superpose eq6494 eq10 -- superposition 10,6494, 6494 into 10, unify on (0).2 in 6494 and (0).2 in 10
  subsumption eq6860 rfl


@[equational_result]
theorem Equation2609_implies_Equation255 (G : Type*) [Magma G] (h : Equation2609 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq19 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation2609_implies_Equation283 (G : Type*) [Magma G] (h : Equation2609 G) : Equation283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2484_implies_Equation211 (G : Type*) [Magma G] (h : Equation2484 G) : Equation211 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2406_implies_Equation231 (G : Type*) [Magma G] (h : Equation2406 G) : Equation231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2372_implies_Equation2266 (G : Type*) [Magma G] (h : Equation2372 G) : Equation2266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = ((X3 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq36 : sK0 ≠ sK0 := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation2368_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2368 G) : Equation2303 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq49 (X2 X3 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X3) = X3 := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).1.1.1 in 28
  have eq74 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation2259_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2259 G) : Equation2246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2259_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2259 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2259_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2259 G) : Equation2249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1975_implies_Equation2035 (G : Type*) [Magma G] (h : Equation1975 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1975_implies_Equation2134 (G : Type*) [Magma G] (h : Equation1975 G) : Equation2134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation1258_implies_Equation104 (G : Type*) [Magma G] (h : Equation1258 G) : Equation104 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation3566_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3566 G) : Equation3759 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X2 X3 X4 : G) : (X3 ◇ X4) = ((X2 ◇ X3) ◇ X4) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq35 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq35 eq23


@[equational_result]
theorem Equation3566_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3566 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X2 X3 X4 : G) : (X3 ◇ X4) = ((X2 ◇ X3) ◇ X4) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq35 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq35 eq23


@[equational_result]
theorem Equation3566_implies_Equation3803 (G : Type*) [Magma G] (h : Equation3566 G) : Equation3803 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X2 X3 X4 : G) : (X3 ◇ X4) = ((X2 ◇ X3) ◇ X4) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq35 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq35 eq23


@[equational_result]
theorem Equation821_implies_Equation99 (G : Type*) [Magma G] (h : Equation821 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation821_implies_Equation100 (G : Type*) [Magma G] (h : Equation821 G) : Equation100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


