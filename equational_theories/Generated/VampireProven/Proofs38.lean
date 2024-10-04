import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

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
theorem Equation266_implies_Equation307 (G : Type*) [Magma G] (h : Equation266 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation266_implies_Equation3306 (G : Type*) [Magma G] (h : Equation266 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation3277_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3295 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq51 eq28


@[equational_result]
theorem Equation3277_implies_Equation3263 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq51 eq28


@[equational_result]
theorem Equation3277_implies_Equation3299 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3299 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq51 eq28


@[equational_result]
theorem Equation3277_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq58 eq28


@[equational_result]
theorem Equation3277_implies_Equation3265 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq58 eq28


@[equational_result]
theorem Equation3277_implies_Equation3304 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := mod_symm nh
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X0) = (X4 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq18 -- superposition 18,28, 28 into 18, unify on (0).2 in 28 and (0).2 in 18
  subsumption eq58 eq28


@[equational_result]
theorem Equation856_implies_Equation47 (G : Type*) [Magma G] (h : Equation856 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation856_implies_Equation55 (G : Type*) [Magma G] (h : Equation856 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1470_implies_Equation3083 (G : Type*) [Magma G] (h : Equation1470 G) : Equation3083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 eq75


@[equational_result]
theorem Equation1470_implies_Equation4131 (G : Type*) [Magma G] (h : Equation1470 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


@[equational_result]
theorem Equation1470_implies_Equation4135 (G : Type*) [Magma G] (h : Equation1470 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq99 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq75 eq10 -- superposition 10,75, 75 into 10, unify on (0).2 in 75 and (0).2 in 10
  subsumption eq99 rfl


@[equational_result]
theorem Equation1470_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq52 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  have eq69 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq76 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq69 eq13 -- backward demodulation 13,69
  subsumption eq52 eq76


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
theorem Equation1470_implies_Equation3459 (G : Type*) [Magma G] (h : Equation1470 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


@[equational_result]
theorem Equation1470_implies_Equation2485 (G : Type*) [Magma G] (h : Equation1470 G) : Equation2485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1470_implies_Equation2447 (G : Type*) [Magma G] (h : Equation1470 G) : Equation2447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X3 ◇ (X4 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0)))) := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2.2.2.2.2 in 11
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq38 (X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X3 ◇ (X4 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq24 eq20 -- backward demodulation 20,24
  have eq39 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ X0) = X2 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq77 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq38 eq58 -- forward demodulation 58,38
  have eq113 : sK0 ≠ sK0 := superpose eq77 eq39 -- superposition 39,77, 77 into 39, unify on (0).2 in 77 and (0).2 in 39
  subsumption eq113 rfl


@[equational_result]
theorem Equation1470_implies_Equation3518 (G : Type*) [Magma G] (h : Equation1470 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


@[equational_result]
theorem Equation1470_implies_Equation4073 (G : Type*) [Magma G] (h : Equation1470 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


@[equational_result]
theorem Equation1470_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.1 in 8
  have eq23 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.2 in 10
  have eq46 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq8 eq23 -- superposition 23,8, 8 into 23, unify on (0).2 in 8 and (0).2.2 in 23
  have eq67 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq46 eq17 -- backward demodulation 17,46
  have eq74 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq67 eq12 -- backward demodulation 12,67
  have eq98 : sK0 ≠ sK0 := superpose eq74 eq9 -- superposition 9,74, 74 into 9, unify on (0).2 in 74 and (0).2 in 9
  subsumption eq98 rfl


@[equational_result]
theorem Equation1470_implies_Equation1861 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
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
theorem Equation1470_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
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
theorem Equation1470_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
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
theorem Equation1470_implies_Equation3526 (G : Type*) [Magma G] (h : Equation1470 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


@[equational_result]
theorem Equation1470_implies_Equation4146 (G : Type*) [Magma G] (h : Equation1470 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1 in 9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq24 -- superposition 24,9, 9 into 24, unify on (0).2 in 9 and (0).2.2 in 24
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq47 eq18 -- backward demodulation 18,47
  have eq75 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq68 eq13 -- backward demodulation 13,68
  have eq78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq75 eq10 -- backward demodulation 10,75
  subsumption eq78 rfl


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
theorem Equation655_implies_Equation1036 (G : Type*) [Magma G] (h : Equation655 G) : Equation1036 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 eq35


@[equational_result]
theorem Equation655_implies_Equation4341 (G : Type*) [Magma G] (h : Equation655 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq49 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq49 eq35


@[equational_result]
theorem Equation655_implies_Equation846 (G : Type*) [Magma G] (h : Equation655 G) : Equation846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 eq35


@[equational_result]
theorem Equation655_implies_Equation842 (G : Type*) [Magma G] (h : Equation655 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 eq35


@[equational_result]
theorem Equation655_implies_Equation823 (G : Type*) [Magma G] (h : Equation655 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq74 : sK0 ≠ sK0 := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation655_implies_Equation3729 (G : Type*) [Magma G] (h : Equation655 G) : Equation3729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq77 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation655_implies_Equation658 (G : Type*) [Magma G] (h : Equation655 G) : Equation658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3))) = X2 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.2.1 in 12
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq46 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))) = X2 := superpose eq35 eq31 -- backward demodulation 31,35
  have eq102 : sK0 ≠ sK0 := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq102 rfl


@[equational_result]
theorem Equation655_implies_Equation3315 (G : Type*) [Magma G] (h : Equation655 G) : Equation3315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 rfl


@[equational_result]
theorem Equation655_implies_Equation3915 (G : Type*) [Magma G] (h : Equation655 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq49 rfl


@[equational_result]
theorem Equation655_implies_Equation3870 (G : Type*) [Magma G] (h : Equation655 G) : Equation3870 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq49 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq49 rfl


@[equational_result]
theorem Equation655_implies_Equation1049 (G : Type*) [Magma G] (h : Equation655 G) : Equation1049 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 eq35


@[equational_result]
theorem Equation655_implies_Equation3319 (G : Type*) [Magma G] (h : Equation655 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq58 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq58 rfl


@[equational_result]
theorem Equation655_implies_Equation1020 (G : Type*) [Magma G] (h : Equation655 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq34 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.2 in 11
  have eq48 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq34 eq9 -- backward demodulation 9,34
  subsumption eq48 eq34


@[equational_result]
theorem Equation655_implies_Equation411 (G : Type*) [Magma G] (h : Equation655 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq34 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.2 in 11
  have eq48 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq34 eq9 -- backward demodulation 9,34
  subsumption eq48 eq34


@[equational_result]
theorem Equation655_implies_Equation3943 (G : Type*) [Magma G] (h : Equation655 G) : Equation3943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq35 eq10 -- backward demodulation 10,35
  subsumption eq49 rfl


@[equational_result]
theorem Equation3798_implies_Equation4452 (G : Type*) [Magma G] (h : Equation3798 G) : Equation4452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = ((X1 ◇ X3) ◇ (X5 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X3)) = ((X5 ◇ X4) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X3)) = (X4 ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq29 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq29 rfl


@[equational_result]
theorem Equation3798_implies_Equation4416 (G : Type*) [Magma G] (h : Equation3798 G) : Equation4416 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = ((X1 ◇ X3) ◇ (X5 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X3)) = ((X5 ◇ X4) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X3)) = (X4 ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3798_implies_Equation4525 (G : Type*) [Magma G] (h : Equation3798 G) : Equation4525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = ((X1 ◇ X3) ◇ (X5 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X3)) = ((X5 ◇ X4) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X3)) = (X4 ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq33 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK2) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation3798_implies_Equation4559 (G : Type*) [Magma G] (h : Equation3798 G) : Equation4559 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X3 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = ((X1 ◇ X3) ◇ (X5 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X3)) = ((X5 ◇ X4) ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (X3 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X3)) = (X4 ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq33 : (sK0 ◇ sK2) ≠ (sK0 ◇ sK2) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq33 rfl


@[equational_result]
theorem Equation2979_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2979 G) : Equation1894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq96 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).1.2.2 in 35
  have eq227 : sK0 ≠ sK0 := superpose eq96 eq10 -- superposition 10,96, 96 into 10, unify on (0).2 in 96 and (0).2 in 10
  subsumption eq227 rfl


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
theorem Equation2979_implies_Equation1635 (G : Type*) [Magma G] (h : Equation2979 G) : Equation1635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ X2) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq76 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X0)) := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2.2 in 10
  have eq130 (X0 : G) : sK0 ≠ (((X0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) := superpose eq35 eq76 -- superposition 76,35, 35 into 76, unify on (0).2 in 35 and (0).2 in 76
  subsumption eq130 eq9


@[equational_result]
theorem Equation4417_implies_Equation4651 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK3 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 : G) : (sK1 ◇ (sK1 ◇ X0)) ≠ (sK3 ◇ (sK3 ◇ X1)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1 in 17
  have eq113 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = ((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).1.1 in 13
  have eq157 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ X5)) = (((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ (X4 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq12421 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (((X2 ◇ X1) ◇ X2) ◇ X1) := superpose eq113 eq157 -- superposition 157,113, 113 into 157, unify on (0).2 in 113 and (0).2 in 157
  have eq12681 (X1 X2 X3 : G) : (sK3 ◇ (sK3 ◇ X3)) ≠ (((X1 ◇ X2) ◇ X1) ◇ X2) := superpose eq12421 eq18 -- superposition 18,12421, 12421 into 18, unify on (0).2 in 12421 and (0).1 in 18
  subsumption eq12681 eq12421


@[equational_result]
theorem Equation4417_implies_Equation4631 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 : G) : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X0 X1 : G) : (sK1 ◇ (sK1 ◇ X0)) ≠ (sK2 ◇ (sK2 ◇ X1)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1 in 17
  have eq113 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = ((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).1.1 in 13
  have eq157 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ X5)) = (((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ (X4 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2.1 in 15
  have eq12455 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (((X2 ◇ X1) ◇ X2) ◇ X1) := superpose eq113 eq157 -- superposition 157,113, 113 into 157, unify on (0).2 in 113 and (0).2 in 157
  have eq12715 (X1 X2 X3 : G) : (sK2 ◇ (sK2 ◇ X3)) ≠ (((X1 ◇ X2) ◇ X1) ◇ X2) := superpose eq12455 eq18 -- superposition 18,12455, 12455 into 18, unify on (0).2 in 12455 and (0).1 in 18
  subsumption eq12715 eq12455


@[equational_result]
theorem Equation4417_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4389 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK1 ◇ (sK1 ◇ X0)) ◇ sK1)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq361 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK1 ◇ X0) ◇ X2)) ◇ X1) := superpose eq361 eq274 -- superposition 274,361, 361 into 274, unify on (0).2 in 361 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4308 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq39 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq55 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  have eq250 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq39 eq13 -- superposition 13,39, 39 into 13, unify on (0).2 in 39 and (0).1.1 in 13
  have eq316 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq8307 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X3) := superpose eq316 eq250 -- superposition 250,316, 316 into 250, unify on (0).2 in 316 and (0).2 in 250
  have eq8505 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X4)) = ((X2 ◇ (X0 ◇ X3)) ◇ X2) := superpose eq250 eq8307 -- superposition 8307,250, 250 into 8307, unify on (0).2 in 250 and (0).2 in 8307
  have eq8524 (X1 X2 X3 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ X2) ◇ X3)) ◇ X1) := superpose eq8307 eq55 -- superposition 55,8307, 8307 into 55, unify on (0).2 in 8307 and (0).2 in 55
  subsumption eq8524 eq8505


@[equational_result]
theorem Equation4417_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ (sK2 ◇ X0)) ◇ sK2)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq361 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq361 eq274 -- superposition 274,361, 361 into 274, unify on (0).2 in 361 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4382 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK1 ◇ (sK1 ◇ X0)) ◇ sK1)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK1 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK1 ◇ (sK1 ◇ X0)) ◇ sK1)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK1 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4421 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4421 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK1) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK1 ◇ (sK1 ◇ X0)) ◇ sK1)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8132 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK1 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8260 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8132 -- superposition 8132,44, 44 into 8132, unify on (0).2 in 44 and (0).2.1 in 8132
  have eq8511 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8260 -- superposition 8260,250, 250 into 8260, unify on (0).2 in 250 and (0).2 in 8260
  subsumption eq8511 rfl


@[equational_result]
theorem Equation4417_implies_Equation4412 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4412 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ (sK2 ◇ X0)) ◇ sK2)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8550 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8678 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8550 -- superposition 8550,44, 44 into 8550, unify on (0).2 in 44 and (0).2.1 in 8550
  have eq8929 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8678 -- superposition 8678,250, 250 into 8678, unify on (0).2 in 250 and (0).2 in 8678
  subsumption eq8929 rfl


@[equational_result]
theorem Equation4417_implies_Equation4401 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4401 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ (sK2 ◇ X0)) ◇ sK2)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4392 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4392 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK2 ◇ (sK2 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ sK2) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK2 ◇ (sK2 ◇ X0)) ◇ sK2)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq8557 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X1 ◇ ((sK2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq8685 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq8557 -- superposition 8557,44, 44 into 8557, unify on (0).2 in 44 and (0).2.1 in 8557
  have eq8936 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq8685 -- superposition 8685,250, 250 into 8685, unify on (0).2 in 250 and (0).2 in 8685
  subsumption eq8936 rfl


@[equational_result]
theorem Equation4417_implies_Equation4429 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4429 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK2 ◇ sK3) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq17 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK3 ◇ (sK3 ◇ X0)) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq19 (X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ sK3) ◇ X1) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq44 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq250 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq274 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK3 ◇ (sK3 ◇ X0)) ◇ sK3)) ◇ X1) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2 in 19
  have eq358 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq44 eq13 -- superposition 13,44, 44 into 13, unify on (0).2 in 44 and (0).1.1 in 13
  have eq9023 (X0 X1 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X1 ◇ ((sK3 ◇ X0) ◇ X2)) ◇ X1) := superpose eq358 eq274 -- superposition 274,358, 358 into 274, unify on (0).2 in 358 and (0).2 in 274
  have eq9151 (X0 X1 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq44 eq9023 -- superposition 9023,44, 44 into 9023, unify on (0).2 in 44 and (0).2.1 in 9023
  have eq9402 (X0 X2 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ X2)) := superpose eq250 eq9151 -- superposition 9151,250, 250 into 9151, unify on (0).2 in 250 and (0).2 in 9151
  subsumption eq9402 rfl


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
theorem Equation1738_implies_Equation4599 (G : Type*) [Magma G] (h : Equation1738 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = ((X3 ◇ X3) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq18


@[equational_result]
theorem Equation1738_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1738 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq25 (X0 : G) : sK0 ≠ (sK0 ◇ (((X0 ◇ X0) ◇ sK0) ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.1 in 10
  have eq30 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  subsumption eq25 eq30


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
theorem Equation1738_implies_Equation4666 (G : Type*) [Magma G] (h : Equation1738 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq25 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq12


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
theorem Equation3874_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3874 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1.2 in 8
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = ((X0 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq258 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq164 eq14 -- superposition 14,164, 164 into 14, unify on (0).2 in 164 and (0).1.1.2 in 14
  have eq309 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ X2) ◇ X0) := superpose eq14 eq258 -- forward demodulation 258,14
  have eq347 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq309 eq9 -- superposition 9,309, 309 into 9, unify on (0).2 in 309 and (0).2 in 9
  have eq416 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq115 -- superposition 115,12, 12 into 115, unify on (0).2 in 12 and (0).2.1 in 115
  have eq664 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq416 eq347 -- superposition 347,416, 416 into 347, unify on (0).2 in 416 and (0).2 in 347
  subsumption eq664 rfl


@[equational_result]
theorem Equation3874_implies_Equation4065 (G : Type*) [Magma G] (h : Equation3874 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1.2 in 8
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq164 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq236 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq164 eq9 -- superposition 9,164, 164 into 9, unify on (0).2 in 164 and (0).2 in 9
  have eq343 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq115 -- superposition 115,12, 12 into 115, unify on (0).2 in 12 and (0).2.1 in 115
  have eq427 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq343 eq236 -- superposition 236,343, 343 into 236, unify on (0).2 in 343 and (0).2 in 236
  subsumption eq427 rfl


@[equational_result]
theorem Equation3874_implies_Equation4068 (G : Type*) [Magma G] (h : Equation3874 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ (X3 ◇ X4)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.1 in 14
  have eq212 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq11 eq165 -- superposition 165,11, 11 into 165, unify on (0).2 in 11 and (0).2 in 165
  have eq214 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq259 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).2.1.2 in 15
  have eq310 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ X2) ◇ X0) := superpose eq15 eq259 -- forward demodulation 259,15
  have eq315 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq362 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq310 eq11 -- superposition 11,310, 310 into 11, unify on (0).2 in 310 and (0).2.1 in 11
  have eq416 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.1 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq470 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq461 eq212 -- backward demodulation 212,461
  have eq474 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose eq470 eq362 -- backward demodulation 362,470
  have eq905 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq474 eq10 -- superposition 10,474, 474 into 10, unify on (0).2 in 474 and (0).2 in 10
  subsumption eq905 rfl


@[equational_result]
theorem Equation3874_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3874 G) : Equation3660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq165 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).1.1 in 14
  have eq214 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq165 -- superposition 165,9, 9 into 165, unify on (0).2 in 9 and (0).2 in 165
  have eq259 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq165 eq15 -- superposition 15,165, 165 into 15, unify on (0).2 in 165 and (0).1.1.2 in 15
  have eq310 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = ((X2 ◇ X2) ◇ X0) := superpose eq15 eq259 -- forward demodulation 259,15
  have eq315 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq310 eq214 -- backward demodulation 214,310
  have eq416 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq116 -- superposition 116,13, 13 into 116, unify on (0).2 in 13 and (0).2.1 in 116
  have eq461 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq416 eq315 -- backward demodulation 315,416
  have eq694 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq461 eq10 -- superposition 10,461, 461 into 10, unify on (0).2 in 461 and (0).2 in 10
  subsumption eq694 rfl


@[equational_result]
theorem Equation3874_implies_Equation359 (G : Type*) [Magma G] (h : Equation3874 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1.2 in 8
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq415 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq115 -- superposition 115,12, 12 into 115, unify on (0).2 in 12 and (0).2.1 in 115
  have eq523 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq415 eq9 -- superposition 9,415, 415 into 9, unify on (0).2 in 415 and (0).2 in 9
  subsumption eq523 rfl


@[equational_result]
theorem Equation864_implies_Equation635 (G : Type*) [Magma G] (h : Equation864 G) : Equation635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation864_implies_Equation645 (G : Type*) [Magma G] (h : Equation864 G) : Equation645 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation864_implies_Equation378 (G : Type*) [Magma G] (h : Equation864 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation864_implies_Equation4131 (G : Type*) [Magma G] (h : Equation864 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq21 eq16


@[equational_result]
theorem Equation864_implies_Equation657 (G : Type*) [Magma G] (h : Equation864 G) : Equation657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation864_implies_Equation58 (G : Type*) [Magma G] (h : Equation864 G) : Equation58 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation864_implies_Equation661 (G : Type*) [Magma G] (h : Equation864 G) : Equation661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1056_implies_Equation436 (G : Type*) [Magma G] (h : Equation1056 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1056_implies_Equation819 (G : Type*) [Magma G] (h : Equation1056 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq42 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation1056_implies_Equation1861 (G : Type*) [Magma G] (h : Equation1056 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1056_implies_Equation3928 (G : Type*) [Magma G] (h : Equation1056 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1056_implies_Equation823 (G : Type*) [Magma G] (h : Equation1056 G) : Equation823 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation1056_implies_Equation4341 (G : Type*) [Magma G] (h : Equation1056 G) : Equation4341 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1056_implies_Equation3721 (G : Type*) [Magma G] (h : Equation1056 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


@[equational_result]
theorem Equation1056_implies_Equation444 (G : Type*) [Magma G] (h : Equation1056 G) : Equation444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1056_implies_Equation3323 (G : Type*) [Magma G] (h : Equation1056 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1056_implies_Equation845 (G : Type*) [Magma G] (h : Equation1056 G) : Equation845 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq47 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1056_implies_Equation848 (G : Type*) [Magma G] (h : Equation1056 G) : Equation848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq47 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1263_implies_Equation1253 (G : Type*) [Magma G] (h : Equation1263 G) : Equation1253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X2 := superpose eq11 eq20 -- forward demodulation 20,11
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation63_implies_Equation2441 (G : Type*) [Magma G] (h : Equation63 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation63_implies_Equation4118 (G : Type*) [Magma G] (h : Equation63 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation63_implies_Equation3050 (G : Type*) [Magma G] (h : Equation63 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation63_implies_Equation1922 (G : Type*) [Magma G] (h : Equation63 G) : Equation1922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation63_implies_Equation4065 (G : Type*) [Magma G] (h : Equation63 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation63_implies_Equation3456 (G : Type*) [Magma G] (h : Equation63 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 rfl


@[equational_result]
theorem Equation63_implies_Equation3522 (G : Type*) [Magma G] (h : Equation63 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation63_implies_Equation1629 (G : Type*) [Magma G] (h : Equation63 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  subsumption eq12 eq11


@[equational_result]
theorem Equation63_implies_Equation23 (G : Type*) [Magma G] (h : Equation63 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation458_implies_Equation378 (G : Type*) [Magma G] (h : Equation458 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation224_implies_Equation3749 (G : Type*) [Magma G] (h : Equation224 G) : Equation3749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation224_implies_Equation2327 (G : Type*) [Magma G] (h : Equation224 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq9


@[equational_result]
theorem Equation224_implies_Equation3769 (G : Type*) [Magma G] (h : Equation224 G) : Equation3769 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq54 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1 in 12
  have eq125 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq54 eq10 -- superposition 10,54, 54 into 10, unify on (0).2 in 54 and (0).2 in 10
  subsumption eq125 rfl


@[equational_result]
theorem Equation224_implies_Equation2330 (G : Type*) [Magma G] (h : Equation224 G) : Equation2330 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq9


@[equational_result]
theorem Equation224_implies_Equation3674 (G : Type*) [Magma G] (h : Equation224 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq49 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation224_implies_Equation3786 (G : Type*) [Magma G] (h : Equation224 G) : Equation3786 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation224_implies_Equation2372 (G : Type*) [Magma G] (h : Equation224 G) : Equation2372 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq44 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq74 : sK0 ≠ sK0 := superpose eq44 eq10 -- superposition 10,44, 44 into 10, unify on (0).2 in 44 and (0).2 in 10
  subsumption eq74 rfl


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
theorem Equation2919_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2919 G) : Equation2862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation257_implies_Equation3253 (G : Type*) [Magma G] (h : Equation257 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq10 eq9 -- backward demodulation 9,10
  subsumption eq11 eq10


@[equational_result]
theorem Equation257_implies_Equation2847 (G : Type*) [Magma G] (h : Equation257 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  subsumption eq11 eq8


@[equational_result]
theorem Equation257_implies_Equation307 (G : Type*) [Magma G] (h : Equation257 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq11 rfl


@[equational_result]
theorem Equation257_implies_Equation2849 (G : Type*) [Magma G] (h : Equation257 G) : Equation2849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


@[equational_result]
theorem Equation439_implies_Equation359 (G : Type*) [Magma G] (h : Equation439 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq14 rfl


@[equational_result]
theorem Equation124_implies_Equation3915 (G : Type*) [Magma G] (h : Equation124 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq20 rfl


@[equational_result]
theorem Equation124_implies_Equation411 (G : Type*) [Magma G] (h : Equation124 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).1 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq15 eq9 -- backward demodulation 9,15
  have eq32 : sK0 ≠ sK0 := superpose eq16 eq19 -- superposition 19,16, 16 into 19, unify on (0).2 in 16 and (0).2 in 19
  subsumption eq32 rfl


@[equational_result]
theorem Equation124_implies_Equation1832 (G : Type*) [Magma G] (h : Equation124 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq19 eq16


@[equational_result]
theorem Equation124_implies_Equation3319 (G : Type*) [Magma G] (h : Equation124 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq20 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq20 rfl


@[equational_result]
theorem Equation124_implies_Equation1629 (G : Type*) [Magma G] (h : Equation124 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq52 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq52 rfl


@[equational_result]
theorem Equation124_implies_Equation151 (G : Type*) [Magma G] (h : Equation124 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq18 -- forward demodulation 18,13
  have eq36 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq36 rfl


@[equational_result]
theorem Equation124_implies_Equation359 (G : Type*) [Magma G] (h : Equation124 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq19 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq19 rfl


@[equational_result]
theorem Equation124_implies_Equation2035 (G : Type*) [Magma G] (h : Equation124 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.1 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq52 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq52 rfl


@[equational_result]
theorem Equation124_implies_Equation1223 (G : Type*) [Magma G] (h : Equation124 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq15 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq8


@[equational_result]
theorem Equation124_implies_Equation1020 (G : Type*) [Magma G] (h : Equation124 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq19 eq16


@[equational_result]
theorem Equation124_implies_Equation8 (G : Type*) [Magma G] (h : Equation124 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2 in 10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2 in 8
  have eq20 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq20 rfl


@[equational_result]
theorem Equation626_implies_Equation622 (G : Type*) [Magma G] (h : Equation626 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq33 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4))) = X3 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2.2.1.1 in 26
  have eq73 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation626_implies_Equation615 (G : Type*) [Magma G] (h : Equation626 G) : Equation615 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq33 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4))) = X3 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2.2.1.1 in 26
  have eq65 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq65 rfl


@[equational_result]
theorem Equation626_implies_Equation624 (G : Type*) [Magma G] (h : Equation626 G) : Equation624 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq33 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4))) = X3 := superpose eq9 eq26 -- superposition 26,9, 9 into 26, unify on (0).2 in 9 and (0).1.2.2.1.1 in 26
  have eq73 : sK0 ≠ sK0 := superpose eq33 eq10 -- superposition 10,33, 33 into 10, unify on (0).2 in 33 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation2351_implies_Equation2266 (G : Type*) [Magma G] (h : Equation2351 G) : Equation2266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation2351_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2351 G) : Equation2406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation2351_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2351 G) : Equation2290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X2 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq11 eq21 -- forward demodulation 21,11
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation645_implies_Equation822 (G : Type*) [Magma G] (h : Equation645 G) : Equation822 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = ((X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq100 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).1.2.2 in 9
  have eq492 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq11 eq41 -- superposition 41,11, 11 into 41, unify on (0).2 in 11 and (0).1 in 41
  have eq913 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) = X2 := superpose eq12 eq492 -- superposition 492,12, 12 into 492, unify on (0).2 in 12 and (0).1.2.2.2 in 492
  have eq914 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := superpose eq18 eq492 -- superposition 492,18, 18 into 492, unify on (0).2 in 18 and (0).1.2.2.2 in 492
  have eq1000 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq100 eq40 -- superposition 40,100, 100 into 40, unify on (0).2 in 100 and (0).1.2.2 in 40
  have eq1107 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X0 := superpose eq11 eq1000 -- forward demodulation 1000,11
  have eq2090 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq913 eq1107 -- superposition 1107,913, 913 into 1107, unify on (0).2 in 913 and (0).1.2.2 in 1107
  have eq3740 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))))) = X0 := superpose eq2090 eq914 -- superposition 914,2090, 2090 into 914, unify on (0).2 in 2090 and (0).1.2.2.2.2 in 914
  have eq3781 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq3740 -- forward demodulation 3740,11
  have eq4012 : sK0 ≠ sK0 := superpose eq3781 eq10 -- superposition 10,3781, 3781 into 10, unify on (0).2 in 3781 and (0).2 in 10
  subsumption eq4012 rfl


@[equational_result]
theorem Equation645_implies_Equation55 (G : Type*) [Magma G] (h : Equation645 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation703_implies_Equation1426 (G : Type*) [Magma G] (h : Equation703 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2 in 8
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1 in 10
  have eq13 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2.2 in 8
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq24 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.2 in 12
  have eq60 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2.2 in 9
  subsumption eq60 eq24


@[equational_result]
theorem Equation703_implies_Equation1434 (G : Type*) [Magma G] (h : Equation703 G) : Equation1434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1.2 in 14
  have eq61 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2 in 10
  subsumption eq61 eq26


@[equational_result]
theorem Equation703_implies_Equation4307 (G : Type*) [Magma G] (h : Equation703 G) : Equation4307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq61 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (X0 ◇ (X0 ◇ sK1)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq61 eq21


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
theorem Equation2890_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2890 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1.2 in 8
  have eq16 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq16 eq9 -- backward demodulation 9,16
  subsumption eq20 eq16


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
theorem Equation3884_implies_Equation3898 (G : Type*) [Magma G] (h : Equation3884 G) : Equation3898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X3 ◇ (X0 ◇ X4)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq40 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK2 ◇ X1)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq103 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2.1 in 17
  have eq111 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.2 in 15
  have eq319 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq111 eq40 -- superposition 40,111, 111 into 40, unify on (0).2 in 111 and (0).2.1 in 40
  subsumption eq319 eq103


@[equational_result]
theorem Equation3884_implies_Equation3888 (G : Type*) [Magma G] (h : Equation3884 G) : Equation3888 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X3 ◇ (X0 ◇ X4)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq40 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK1 ◇ X1)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq103 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2.1 in 17
  have eq111 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq17 eq15 -- superposition 15,17, 17 into 15, unify on (0).2 in 17 and (0).2.2 in 15
  have eq319 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq111 eq40 -- superposition 40,111, 111 into 40, unify on (0).2 in 111 and (0).2.1 in 40
  subsumption eq319 eq103


@[equational_result]
theorem Equation510_implies_Equation3862 (G : Type*) [Magma G] (h : Equation510 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.2.2 in 8
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq15 -- forward demodulation 15,10
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.1 in 11
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq19 eq13 -- backward demodulation 13,19
  have eq39 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq39 rfl


@[equational_result]
theorem Equation510_implies_Equation439 (G : Type*) [Magma G] (h : Equation510 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq16 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2.2 in 9
  have eq17 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq16 -- forward demodulation 16,11
  have eq19 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2.1 in 14
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.1 in 12
  have eq27 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq30 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq20 eq27 -- backward demodulation 27,20
  have eq66 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.2.2.2 in 9
  have eq73 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose eq66 eq10 -- backward demodulation 10,66
  subsumption eq73 eq9


@[equational_result]
theorem Equation661_implies_Equation860 (G : Type*) [Magma G] (h : Equation661 G) : Equation860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation661_implies_Equation852 (G : Type*) [Magma G] (h : Equation661 G) : Equation852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation661_implies_Equation848 (G : Type*) [Magma G] (h : Equation661 G) : Equation848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation661_implies_Equation842 (G : Type*) [Magma G] (h : Equation661 G) : Equation842 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation661_implies_Equation845 (G : Type*) [Magma G] (h : Equation661 G) : Equation845 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation2507_implies_Equation4380 (G : Type*) [Magma G] (h : Equation2507 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq25 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq25 rfl


@[equational_result]
theorem Equation2507_implies_Equation4435 (G : Type*) [Magma G] (h : Equation2507 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq22 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2507_implies_Equation411 (G : Type*) [Magma G] (h : Equation2507 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq13 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq29 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).1.2.1 in 13
  have eq35 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq10 eq29 -- forward demodulation 29,10
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq35 -- forward demodulation 35,11
  have eq48 : sK0 ≠ sK0 := superpose eq36 eq9 -- superposition 9,36, 36 into 9, unify on (0).2 in 36 and (0).2 in 9
  subsumption eq48 rfl


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
theorem Equation3591_implies_Equation3752 (G : Type*) [Magma G] (h : Equation3591 G) : Equation3752 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X2) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
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
  have eq907 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq172 eq10 -- superposition 10,172, 172 into 10, unify on (0).2 in 172 and (0).2 in 10
  have eq946 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := superpose eq697 eq907 -- forward demodulation 907,697
  subsumption eq946 eq354


