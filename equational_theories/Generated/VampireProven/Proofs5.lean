import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation222_implies_Equation4435 (G : Type*) [Magma G] (h : Equation222 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2227_implies_Equation4689 (G : Type*) [Magma G] (h : Equation2227 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq120 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq120 eq26


@[equational_result]
theorem Equation2241_implies_Equation1426 (G : Type*) [Magma G] (h : Equation2241 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq21 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq24 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq15 eq21 -- forward demodulation 21,15
  have eq74 : sK0 ≠ sK0 := superpose eq24 eq9 -- superposition 9,24, 24 into 9, unify on (0).2 in 24 and (0).2 in 9
  subsumption eq74 rfl


@[equational_result]
theorem Equation2241_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2241 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq50 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq50 rfl


@[equational_result]
theorem Equation2241_implies_Equation23 (G : Type*) [Magma G] (h : Equation2241 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1 in 8
  have eq27 : sK0 ≠ sK0 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq27 rfl


@[equational_result]
theorem Equation2241_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2241 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq13 -- forward demodulation 13,8
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq16 rfl


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
theorem Equation2249_implies_Equation205 (G : Type*) [Magma G] (h : Equation2249 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation2251_implies_Equation158 (G : Type*) [Magma G] (h : Equation2251 G) : Equation158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ X3) := superpose eq11 eq12 -- forward demodulation 12,11
  have eq36 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.1 in 11
  have eq46 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq46 rfl


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
theorem Equation2260_implies_Equation159 (G : Type*) [Magma G] (h : Equation2260 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq49 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation2261_implies_Equation1642 (G : Type*) [Magma G] (h : Equation2261 G) : Equation1642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation2270_implies_Equation1427 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq21 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq26 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq21 -- forward demodulation 21,18
  have eq57 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2270_implies_Equation1454 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq20 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2270_implies_Equation1456 (G : Type*) [Magma G] (h : Equation2270 G) : Equation1456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq20 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq25 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq18 eq20 -- forward demodulation 20,18
  have eq57 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq57 rfl


@[equational_result]
theorem Equation2274_implies_Equation2278 (G : Type*) [Magma G] (h : Equation2274 G) : Equation2278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2275_implies_Equation1450 (G : Type*) [Magma G] (h : Equation2275 G) : Equation1450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2278_implies_Equation1460 (G : Type*) [Magma G] (h : Equation2278 G) : Equation1460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq53 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq53 rfl


@[equational_result]
theorem Equation2279_implies_Equation1876 (G : Type*) [Magma G] (h : Equation2279 G) : Equation1876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq93 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq93 rfl


@[equational_result]
theorem Equation228_implies_Equation1045 (G : Type*) [Magma G] (h : Equation228 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation1921 (G : Type*) [Magma G] (h : Equation228 G) : Equation1921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2327 (G : Type*) [Magma G] (h : Equation228 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2540 (G : Type*) [Magma G] (h : Equation228 G) : Equation2540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2743 (G : Type*) [Magma G] (h : Equation228 G) : Equation2743 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq9


@[equational_result]
theorem Equation228_implies_Equation2936 (G : Type*) [Magma G] (h : Equation228 G) : Equation2936 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation228_implies_Equation3 (G : Type*) [Magma G] (h : Equation228 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq8 eq10 -- forward demodulation 10,8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2283_implies_Equation1642 (G : Type*) [Magma G] (h : Equation2283 G) : Equation1642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation228_implies_Equation3887 (G : Type*) [Magma G] (h : Equation228 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq14 rfl


@[equational_result]
theorem Equation2286_implies_Equation1453 (G : Type*) [Magma G] (h : Equation2286 G) : Equation1453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ (X0 ◇ X1)) = X5 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq28 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation229_implies_Equation255 (G : Type*) [Magma G] (h : Equation229 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq18 eq8


@[equational_result]
theorem Equation2294_implies_Equation255 (G : Type*) [Magma G] (h : Equation2294 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.2 in 10
  have eq18 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq23 : sK0 ≠ sK0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq23 rfl


@[equational_result]
theorem Equation229_implies_Equation4380 (G : Type*) [Magma G] (h : Equation229 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).2 in 9
  subsumption eq18 rfl


@[equational_result]
theorem Equation229_implies_Equation47 (G : Type*) [Magma G] (h : Equation229 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation2296_implies_Equation205 (G : Type*) [Magma G] (h : Equation2296 G) : Equation205 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2297_implies_Equation573 (G : Type*) [Magma G] (h : Equation2297 G) : Equation573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X4 ◇ X5)) ◇ (X0 ◇ X1))) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.2.2 in 12
  have eq20 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq23 (X0 X1 X4 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ X4) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.2 in 9
  have eq42 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) = (((X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2))) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.1.2 in 20
  have eq55 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) = X1 := superpose eq23 eq42 -- forward demodulation 42,23
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ X3) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq69 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq109 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq69 eq17 -- backward demodulation 17,69
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq109 eq9 -- backward demodulation 9,109
  have eq130 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := superpose eq109 eq10 -- backward demodulation 10,109
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq109 eq113 -- forward demodulation 113,109
  have eq132 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq109 eq131 -- forward demodulation 131,109
  subsumption eq130 eq132


@[equational_result]
theorem Equation229_implies_Equation99 (G : Type*) [Magma G] (h : Equation229 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq17 eq9 -- backward demodulation 9,17
  subsumption eq18 eq11


@[equational_result]
theorem Equation2306_implies_Equation2774 (G : Type*) [Magma G] (h : Equation2306 G) : Equation2774 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) ◇ X4) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.2 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X3 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.1 in 9
  have eq131 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq52 eq13 -- superposition 13,52, 52 into 13, unify on (0).2 in 52 and (0).1.1.1 in 13
  have eq577 : sK0 ≠ sK0 := superpose eq131 eq10 -- superposition 10,131, 131 into 10, unify on (0).2 in 131 and (0).2 in 10
  subsumption eq577 rfl


@[equational_result]
theorem Equation2307_implies_Equation705 (G : Type*) [Magma G] (h : Equation2307 G) : Equation705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = ((X0 ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) = ((X0 ◇ X3) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq15 eq11 -- backward demodulation 11,15
  have eq37 (X0 X1 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X3 := superpose eq22 eq22 -- superposition 22,22, 22 into 22, unify on (0).2 in 22 and (0).1.2 in 22
  have eq41 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).1.1 in 9
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq41 eq20 -- backward demodulation 20,41
  have eq55 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X4) = X1 := superpose eq22 eq51 -- superposition 51,22, 22 into 51, unify on (0).2 in 22 and (0).1 in 51
  have eq77 (X0 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2.2.2 in 10
  have eq101 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X3 := superpose eq55 eq37 -- backward demodulation 37,55
  have eq104 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq41 eq101 -- forward demodulation 101,41
  subsumption eq77 eq104


@[equational_result]
theorem Equation2308_implies_Equation1764 (G : Type*) [Magma G] (h : Equation2308 G) : Equation1764 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq19 eq11 -- superposition 11,19, 19 into 11, unify on (0).2 in 19 and (0).1.1.1.2 in 11
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq83 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq54 eq10 -- backward demodulation 10,54
  have eq84 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq56 eq55 -- backward demodulation 55,56
  have eq99 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = (((X0 ◇ X0) ◇ X3) ◇ X1) := superpose eq56 eq12 -- superposition 12,56, 56 into 12, unify on (0).2 in 56 and (0).1.2.2.2 in 12
  have eq108 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq99 -- forward demodulation 99,56
  have eq109 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq108 eq12 -- backward demodulation 12,108
  have eq138 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X1))) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq108 eq103 -- forward demodulation 103,108
  have eq139 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq50 eq138 -- forward demodulation 138,50
  have eq144 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq84 -- superposition 84,19, 19 into 84, unify on (0).2 in 19 and (0).1.1 in 84
  have eq149 (X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ X3) := superpose eq144 eq139 -- backward demodulation 139,144
  have eq151 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq149 eq83 -- backward demodulation 83,149
  have eq170 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq109 -- superposition 109,19, 19 into 109, unify on (0).2 in 19 and (0).1.2.2 in 109
  have eq189 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq170 eq151 -- backward demodulation 151,170
  have eq190 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq149 eq189 -- forward demodulation 189,149
  subsumption eq190 eq19


@[equational_result]
theorem Equation2308_implies_Equation543 (G : Type*) [Magma G] (h : Equation2308 G) : Equation543 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X2 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2.2 in 12
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1.2 in 9
  have eq98 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq12 eq56 -- superposition 56,12, 12 into 56, unify on (0).2 in 12 and (0).1 in 56
  have eq107 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq56 eq98 -- forward demodulation 98,56
  have eq108 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ X3)) := superpose eq107 eq12 -- backward demodulation 12,107
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq19 eq108 -- superposition 108,19, 19 into 108, unify on (0).2 in 19 and (0).1.2.2 in 108
  have eq159 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2))) := superpose eq147 eq10 -- backward demodulation 10,147
  have eq160 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := superpose eq54 eq159 -- forward demodulation 159,54
  have eq161 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := superpose eq147 eq160 -- forward demodulation 160,147
  have eq162 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq19 eq161 -- forward demodulation 161,19
  subsumption eq162 eq19


@[equational_result]
theorem Equation2311_implies_Equation724 (G : Type*) [Magma G] (h : Equation2311 G) : Equation724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq28 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.2 in 11
  have eq35 (X1 X3 : G) : X1 = X3 := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).1 in 28
  have eq58 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq28 eq10 -- superposition 10,28, 28 into 10, unify on (0).2 in 28 and (0).2.2.2 in 10
  subsumption eq58 eq35


@[equational_result]
theorem Equation2322_implies_Equation2333 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2333 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X4 ◇ (X5 ◇ X1)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq43 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq34 eq10 -- backward demodulation 10,34
  subsumption eq43 eq11


@[equational_result]
theorem Equation2322_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : ((X4 ◇ (X5 ◇ X1)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2333_implies_Equation2376 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2376 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.2.2 in 9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq58 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X1 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq109 : sK0 ≠ sK0 := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation2333_implies_Equation2739 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2739 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq27 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2333_implies_Equation2778 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2778 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq28 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq28 rfl


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
theorem Equation2338_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2338 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq21 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  subsumption eq21 eq8


@[equational_result]
theorem Equation2338_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2338 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq20 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq20 eq9 -- backward demodulation 9,20
  subsumption eq21 eq8


@[equational_result]
theorem Equation2338_implies_Equation3050 (G : Type*) [Magma G] (h : Equation2338 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2 in 8
  have eq20 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq15 eq8 -- superposition 8,15, 15 into 8, unify on (0).2 in 15 and (0).1.1.2.2 in 8
  have eq21 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := superpose eq20 eq21 -- backward demodulation 21,20
  subsumption eq22 eq8


@[equational_result]
theorem Equation2338_implies_Equation411 (G : Type*) [Magma G] (h : Equation2338 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.2 in 8
  have eq11 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.2 in 10
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq16 : sK0 ≠ sK0 := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2 in 9
  subsumption eq16 rfl


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
theorem Equation2347_implies_Equation228 (G : Type*) [Magma G] (h : Equation2347 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2347_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2347 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


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
theorem Equation2365_implies_Equation1077 (G : Type*) [Magma G] (h : Equation2365 G) : Equation1077 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq25 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq25 eq16


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
theorem Equation2376_implies_Equation2702 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2702 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2376_implies_Equation2782 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 X5 : G) : ((X5 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation238_implies_Equation1055 (G : Type*) [Magma G] (h : Equation238 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 : sK0 ≠ sK0 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  subsumption eq18 rfl


@[equational_result]
theorem Equation2381_implies_Equation228 (G : Type*) [Magma G] (h : Equation2381 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2381_implies_Equation2716 (G : Type*) [Magma G] (h : Equation2381 G) : Equation2716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq28 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X1 := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).1.1.2.2 in 9
  have eq115 : sK0 ≠ sK0 := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation2382_implies_Equation1156 (G : Type*) [Magma G] (h : Equation2382 G) : Equation1156 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq16


@[equational_result]
theorem Equation238_implies_Equation3897 (G : Type*) [Magma G] (h : Equation238 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK0) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq12 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq18 : sK0 ≠ sK0 := superpose eq14 eq11 -- superposition 11,14, 14 into 11, unify on (0).2 in 14 and (0).2 in 11
  subsumption eq18 rfl


@[equational_result]
theorem Equation2385_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2385 G) : Equation2406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.2 in 9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq12 eq20 -- forward demodulation 20,12
  have eq61 : sK0 ≠ sK0 := superpose eq25 eq10 -- superposition 10,25, 25 into 10, unify on (0).2 in 25 and (0).2 in 10
  subsumption eq61 rfl


@[equational_result]
theorem Equation2389_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2389 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1.2 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq68 rfl


@[equational_result]
theorem Equation2398_implies_Equation228 (G : Type*) [Magma G] (h : Equation2398 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq22 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2398_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2398 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq13 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation2402_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2402 G) : Equation2355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq14 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1 in 9
  have eq68 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq68 rfl


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
theorem Equation2415_implies_Equation2753 (G : Type*) [Magma G] (h : Equation2415 G) : Equation2753 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ X3)) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2420_implies_Equation242 (G : Type*) [Magma G] (h : Equation2420 G) : Equation242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation242_implies_Equation2425 (G : Type*) [Magma G] (h : Equation242 G) : Equation2425 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2425_implies_Equation2517 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2517 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2425_implies_Equation2554 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2425_implies_Equation2571 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2571 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2425_implies_Equation2588 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2588 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2425_implies_Equation2623 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq27 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2430_implies_Equation2836 (G : Type*) [Magma G] (h : Equation2430 G) : Equation2836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq12 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2447_implies_Equation1629 (G : Type*) [Magma G] (h : Equation2447 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2450_implies_Equation1426 (G : Type*) [Magma G] (h : Equation2450 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq35


@[equational_result]
theorem Equation2450_implies_Equation151 (G : Type*) [Magma G] (h : Equation2450 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq73 : sK0 ≠ sK0 := superpose eq35 eq9 -- superposition 9,35, 35 into 9, unify on (0).2 in 35 and (0).2 in 9
  subsumption eq73 rfl


@[equational_result]
theorem Equation2450_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2450 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq35


@[equational_result]
theorem Equation2450_implies_Equation203 (G : Type*) [Magma G] (h : Equation2450 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq83 eq9 -- backward demodulation 9,83
  subsumption eq86 eq34


@[equational_result]
theorem Equation2450_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2450 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq86 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq83 eq9 -- backward demodulation 9,83
  have eq87 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq83 eq86 -- forward demodulation 86,83
  subsumption eq87 eq34


@[equational_result]
theorem Equation2450_implies_Equation307 (G : Type*) [Magma G] (h : Equation2450 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq16 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq20 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1 in 11
  have eq21 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.2 in 10
  have eq22 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1.2 in 8
  have eq25 (X0 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq16 -- forward demodulation 16,10
  have eq28 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq20 -- forward demodulation 20,8
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq28 eq25 -- backward demodulation 25,28
  have eq30 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq10 eq21 -- forward demodulation 21,10
  have eq31 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq30 -- forward demodulation 30,28
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq31 eq29 -- backward demodulation 29,31
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq28 eq22 -- forward demodulation 22,28
  have eq35 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq32 -- backward demodulation 32,34
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq35 eq11 -- superposition 11,35, 35 into 11, unify on (0).2 in 35 and (0).1.1.2.1 in 11
  have eq75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq35 eq10 -- superposition 10,35, 35 into 10, unify on (0).2 in 35 and (0).1.2.1 in 10
  have eq76 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq35 eq8 -- superposition 8,35, 35 into 8, unify on (0).2 in 35 and (0).1.1.2.1 in 8
  have eq78 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq75 eq74 -- backward demodulation 74,75
  have eq80 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq76 eq78 -- backward demodulation 78,76
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq80 eq75 -- backward demodulation 75,80
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq35 eq81 -- forward demodulation 81,35
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq82 eq76 -- backward demodulation 76,82
  have eq124 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq83 eq9 -- superposition 9,83, 83 into 9, unify on (0).2 in 83 and (0).2 in 9
  subsumption eq124 rfl


@[equational_result]
theorem Equation2453_implies_Equation2287 (G : Type*) [Magma G] (h : Equation2453 G) : Equation2287 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq18 eq20 -- forward demodulation 20,18
  have eq34 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq33 -- forward demodulation 33,12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X0) := superpose eq34 eq18 -- backward demodulation 18,34
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) := superpose eq36 eq19 -- backward demodulation 19,36
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq36 eq11 -- backward demodulation 11,36
  have eq41 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ X1) = X0 := superpose eq34 eq37 -- forward demodulation 37,34
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq36 eq41 -- forward demodulation 41,36
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq39 -- forward demodulation 39,34
  have eq44 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq43 eq10 -- backward demodulation 10,43
  subsumption eq44 eq42


@[equational_result]
theorem Equation2454_implies_Equation1439 (G : Type*) [Magma G] (h : Equation2454 G) : Equation1439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq14 rfl


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
theorem Equation246_implies_Equation2281 (G : Type*) [Magma G] (h : Equation246 G) : Equation2281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2463_implies_Equation1874 (G : Type*) [Magma G] (h : Equation2463 G) : Equation1874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X1) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq36 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq36 eq29 -- backward demodulation 29,36
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq40 eq26 -- backward demodulation 26,40
  have eq58 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4))) := superpose eq40 eq15 -- backward demodulation 15,40
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq40 eq58 -- forward demodulation 58,40
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq64 eq63 -- backward demodulation 63,64
  have eq66 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK3)) := superpose eq64 eq10 -- backward demodulation 10,64
  have eq119 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq36 eq56 -- superposition 56,36, 36 into 56, unify on (0).2 in 36 and (0).1.2.1 in 56
  have eq309 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := superpose eq65 eq50 -- superposition 50,65, 65 into 50, unify on (0).2 in 65 and (0).1.1 in 50
  have eq331 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := superpose eq119 eq309 -- forward demodulation 309,119
  have eq421 (X0 : G) : sK0 ≠ ((sK0 ◇ (sK1 ◇ X0)) ◇ (sK1 ◇ sK3)) := superpose eq64 eq66 -- superposition 66,64, 64 into 66, unify on (0).2 in 64 and (0).2.1 in 66
  subsumption eq421 eq331


@[equational_result]
theorem Equation2463_implies_Equation2489 (G : Type*) [Magma G] (h : Equation2463 G) : Equation2489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X4))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2 in 9
  have eq36 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X1) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2.1 in 21
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1 in 21
  have eq53 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) = X3 := superpose eq40 eq13 -- backward demodulation 13,40
  have eq62 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) = X3 := superpose eq40 eq53 -- forward demodulation 53,40
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq40 eq41 -- forward demodulation 41,40
  have eq66 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) ◇ sK1) := superpose eq64 eq10 -- backward demodulation 10,64
  have eq161 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq62 eq21 -- superposition 21,62, 62 into 21, unify on (0).2 in 62 and (0).2.1 in 21
  have eq175 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq161 eq66 -- backward demodulation 66,161
  subsumption eq175 eq36


@[equational_result]
theorem Equation2464_implies_Equation1844 (G : Type*) [Magma G] (h : Equation2464 G) : Equation1844 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq24 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 rfl


@[equational_result]
theorem Equation2473_implies_Equation1630 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation1657 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation1659 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq18 eq11 -- backward demodulation 11,18
  have eq27 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation2473_implies_Equation1873 (G : Type*) [Magma G] (h : Equation2473 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq18 eq9 -- backward demodulation 9,18
  have eq22 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq22 rfl


@[equational_result]
theorem Equation2473_implies_Equation3523 (G : Type*) [Magma G] (h : Equation2473 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ X1) := superpose eq12 eq13 -- forward demodulation 13,12
  have eq74 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).1 in 10
  subsumption eq74 rfl


@[equational_result]
theorem Equation2477_implies_Equation1663 (G : Type*) [Magma G] (h : Equation2477 G) : Equation1663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq13 eq11 -- backward demodulation 11,13
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1 in 16
  have eq184 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq184 rfl


@[equational_result]
theorem Equation2478_implies_Equation164 (G : Type*) [Magma G] (h : Equation2478 G) : Equation164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq23 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation2478_implies_Equation1855 (G : Type*) [Magma G] (h : Equation2478 G) : Equation1855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2481_implies_Equation1655 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq35 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 eq12


@[equational_result]
theorem Equation2481_implies_Equation1661 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq35 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq35 eq12


@[equational_result]
theorem Equation2481_implies_Equation1873 (G : Type*) [Magma G] (h : Equation2481 G) : Equation1873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation2481_implies_Equation3525 (G : Type*) [Magma G] (h : Equation2481 G) : Equation3525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).1 in 10
  subsumption eq36 rfl


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
theorem Equation2485_implies_Equation1632 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq40 eq10 -- superposition 10,40, 40 into 10, unify on (0).2 in 40 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2485_implies_Equation1654 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2485_implies_Equation1662 (G : Type*) [Magma G] (h : Equation2485 G) : Equation1662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq69 : sK0 ≠ sK0 := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2 in 10
  subsumption eq69 rfl


@[equational_result]
theorem Equation2486_implies_Equation2490 (G : Type*) [Magma G] (h : Equation2486 G) : Equation2490 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.2 in 11
  have eq21 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq21 eq13


@[equational_result]
theorem Equation2493_implies_Equation255 (G : Type*) [Magma G] (h : Equation2493 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2499_implies_Equation1041 (G : Type*) [Magma G] (h : Equation2499 G) : Equation1041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq50 : sK0 ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq58 eq50 -- superposition 50,58, 58 into 50, unify on (0).2 in 58 and (0).2 in 50
  subsumption eq77 rfl


@[equational_result]
theorem Equation2499_implies_Equation1904 (G : Type*) [Magma G] (h : Equation2499 G) : Equation1904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq73 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := superpose eq57 eq10 -- backward demodulation 10,57
  subsumption eq73 eq47


@[equational_result]
theorem Equation2499_implies_Equation2322 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq79 : sK0 ≠ sK0 := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  subsumption eq79 rfl


@[equational_result]
theorem Equation2499_implies_Equation2415 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq36 eq20 -- backward demodulation 20,36
  have eq99 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq46 eq49 -- superposition 49,46, 46 into 49, unify on (0).2 in 46 and (0).1 in 49
  have eq176 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X2 := superpose eq99 eq49 -- superposition 49,99, 99 into 49, unify on (0).2 in 99 and (0).1 in 49
  have eq341 : sK0 ≠ sK0 := superpose eq176 eq10 -- superposition 10,176, 176 into 10, unify on (0).2 in 176 and (0).2 in 10
  subsumption eq341 rfl


@[equational_result]
theorem Equation2499_implies_Equation3108 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq25 -- backward demodulation 25,36
  have eq50 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq63 : sK0 ≠ sK0 := superpose eq48 eq50 -- superposition 50,48, 48 into 50, unify on (0).2 in 48 and (0).2 in 50
  subsumption eq63 rfl


@[equational_result]
theorem Equation2499_implies_Equation3803 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3803 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq23 -- superposition 23,11, 11 into 23, unify on (0).2 in 11 and (0).1.1.2 in 23
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq35 -- backward demodulation 35,36
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq26 -- backward demodulation 26,36
  have eq101 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq47 -- superposition 47,46, 46 into 47, unify on (0).2 in 46 and (0).1.1.2 in 47
  have eq246 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq101 eq10 -- superposition 10,101, 101 into 10, unify on (0).2 in 101 and (0).2 in 10
  subsumption eq246 rfl


@[equational_result]
theorem Equation2499_implies_Equation3883 (G : Type*) [Magma G] (h : Equation2499 G) : Equation3883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.2.1 in 9
  have eq36 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq9 eq23 -- superposition 23,9, 9 into 23, unify on (0).2 in 9 and (0).1.1 in 23
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq36 eq28 -- backward demodulation 28,36
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq36 eq27 -- backward demodulation 27,36
  have eq50 : sK0 ≠ (sK0 ◇ sK0) := superpose eq47 eq10 -- backward demodulation 10,47
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq12 -- superposition 12,48, 48 into 12, unify on (0).2 in 48 and (0).1.1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq58 eq50 -- superposition 50,58, 58 into 50, unify on (0).2 in 58 and (0).2 in 50
  subsumption eq77 rfl


@[equational_result]
theorem Equation2500_implies_Equation291 (G : Type*) [Magma G] (h : Equation2500 G) : Equation291 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq48 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq40 eq10 -- backward demodulation 10,40
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq12 eq40 -- superposition 40,12, 12 into 40, unify on (0).2 in 12 and (0).2 in 40
  have eq75 (X1 X2 : G) : X1 = X2 := superpose eq52 eq52 -- superposition 52,52, 52 into 52, unify on (0).2 in 52 and (0).1 in 52
  have eq90 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq52 eq48 -- superposition 48,52, 52 into 48, unify on (0).2 in 52 and (0).2.1.1 in 48
  subsumption eq90 eq75


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
theorem Equation2509_implies_Equation2923 (G : Type*) [Magma G] (h : Equation2509 G) : Equation2923 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq26 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq26 eq17


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
theorem Equation2517_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation2517_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq44 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq44 rfl


@[equational_result]
theorem Equation2521_implies_Equation2420 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2420 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq89 : sK0 ≠ ((sK2 ◇ (sK3 ◇ sK1)) ◇ sK0) := superpose eq83 eq10 -- backward demodulation 10,83
  subsumption eq89 eq83


@[equational_result]
theorem Equation2521_implies_Equation2808 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2808 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq87 : sK0 ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq82 eq10 -- backward demodulation 10,82
  subsumption eq87 eq82


@[equational_result]
theorem Equation2521_implies_Equation2964 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq75 eq9 -- backward demodulation 9,75
  have eq88 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  have eq95 : sK0 ≠ (sK2 ◇ sK0) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq99 : sK0 ≠ sK0 := superpose eq88 eq95 -- superposition 95,88, 88 into 95, unify on (0).2 in 88 and (0).2 in 95
  subsumption eq99 rfl


@[equational_result]
theorem Equation2521_implies_Equation2998 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2998 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq70 eq9 -- backward demodulation 9,70
  have eq83 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq70 eq12 -- backward demodulation 12,70
  have eq87 : sK0 ≠ (sK2 ◇ sK0) := superpose eq82 eq10 -- backward demodulation 10,82
  have eq90 : sK0 ≠ sK0 := superpose eq83 eq87 -- superposition 87,83, 83 into 87, unify on (0).2 in 83 and (0).2 in 87
  subsumption eq90 rfl


@[equational_result]
theorem Equation2521_implies_Equation3163 (G : Type*) [Magma G] (h : Equation2521 G) : Equation3163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.1.1 in 12
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq35 -- forward demodulation 35,16
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq12 -- superposition 12,39, 39 into 12, unify on (0).2 in 39 and (0).1.1 in 12
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq57 eq16 -- backward demodulation 16,57
  have eq82 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0) := superpose eq57 eq10 -- backward demodulation 10,57
  have eq89 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq75 eq12 -- backward demodulation 12,75
  subsumption eq82 eq89


@[equational_result]
theorem Equation2536_implies_Equation2558 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1.2.1 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).1 in 21
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq74 eq68 -- superposition 68,74, 74 into 68, unify on (0).2 in 74 and (0).1.1.1 in 68
  have eq246 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq224 -- forward demodulation 224,12
  have eq345 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq246 eq13 -- superposition 13,246, 246 into 13, unify on (0).2 in 246 and (0).1.1.1.2 in 13
  have eq355 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq246 eq9 -- superposition 9,246, 246 into 9, unify on (0).2 in 246 and (0).1.1.2 in 9
  have eq364 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq74 eq355 -- forward demodulation 355,74
  have eq370 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq364 eq246 -- backward demodulation 246,364
  have eq375 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq364 eq345 -- backward demodulation 345,364
  have eq409 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) = X1 := superpose eq370 eq375 -- forward demodulation 375,370
  have eq410 (X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X1 := superpose eq364 eq409 -- forward demodulation 409,364
  have eq1499 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1577 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq364 eq1499 -- forward demodulation 1499,364
  have eq1663 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq1577 eq9 -- superposition 9,1577, 1577 into 9, unify on (0).2 in 1577 and (0).1.1.2 in 9
  have eq2627 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq1663 eq410 -- superposition 410,1663, 1663 into 410, unify on (0).2 in 1663 and (0).1.1 in 410
  have eq4682 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = X1 := superpose eq2627 eq9 -- superposition 9,2627, 2627 into 9, unify on (0).2 in 2627 and (0).1.1.2 in 9
  have eq5036 : sK0 ≠ sK0 := superpose eq4682 eq10 -- superposition 10,4682, 4682 into 10, unify on (0).2 in 4682 and (0).2 in 10
  subsumption eq5036 rfl


@[equational_result]
theorem Equation2536_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq76 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2.1 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq374 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq363 eq76 -- backward demodulation 76,363
  have eq1106 : sK0 ≠ sK0 := superpose eq374 eq10 -- superposition 10,374, 374 into 10, unify on (0).2 in 374 and (0).2 in 10
  subsumption eq1106 rfl


@[equational_result]
theorem Equation2536_implies_Equation3093 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq1497 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1554 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq363 eq1497 -- forward demodulation 1497,363
  have eq1590 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq373 eq1554 -- superposition 1554,373, 373 into 1554, unify on (0).2 in 373 and (0).1.1.2 in 1554
  have eq1910 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq1590 eq9 -- superposition 9,1590, 1590 into 9, unify on (0).2 in 1590 and (0).1.1.2 in 9
  have eq2321 : sK0 ≠ sK0 := superpose eq1910 eq10 -- superposition 10,1910, 1910 into 10, unify on (0).2 in 1910 and (0).2 in 10
  subsumption eq2321 rfl


@[equational_result]
theorem Equation2536_implies_Equation3145 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3145 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq391 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq363 eq10 -- backward demodulation 10,363
  subsumption eq391 eq373


@[equational_result]
theorem Equation2536_implies_Equation3180 (G : Type*) [Magma G] (h : Equation2536 G) : Equation3180 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1.2 in 11
  have eq21 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.1.2 in 21
  have eq55 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).1.1 in 11
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq55 eq21 -- superposition 21,55, 55 into 21, unify on (0).2 in 55 and (0).2.1.2 in 21
  have eq70 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq55 eq11 -- superposition 11,55, 55 into 11, unify on (0).2 in 55 and (0).1.1.1.2 in 11
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq68 eq9 -- superposition 9,68, 68 into 9, unify on (0).2 in 68 and (0).1.1.2.1 in 9
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq130 -- forward demodulation 130,12
  have eq340 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq144 eq9 -- superposition 9,144, 144 into 9, unify on (0).2 in 144 and (0).1.1.2 in 9
  have eq363 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq68 eq340 -- forward demodulation 340,68
  have eq373 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq363 eq70 -- backward demodulation 70,363
  have eq1497 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq64 eq9 -- superposition 9,64, 64 into 9, unify on (0).2 in 64 and (0).1.1 in 9
  have eq1554 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq363 eq1497 -- forward demodulation 1497,363
  have eq1590 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq373 eq1554 -- superposition 1554,373, 373 into 1554, unify on (0).2 in 373 and (0).1.1.2 in 1554
  have eq1933 : sK0 ≠ sK0 := superpose eq1590 eq10 -- superposition 10,1590, 1590 into 10, unify on (0).2 in 1590 and (0).2 in 10
  subsumption eq1933 rfl


@[equational_result]
theorem Equation2537_implies_Equation2092 (G : Type*) [Magma G] (h : Equation2537 G) : Equation2092 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2.1 in 9
  have eq20 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq16 eq11 -- backward demodulation 11,16
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq18 -- forward demodulation 18,12
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1.2.2.1 in 25
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq28 -- forward demodulation 28,16
  have eq46 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq44 eq16 -- backward demodulation 16,44
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq46 eq26 -- backward demodulation 26,46
  have eq52 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq46 eq20 -- backward demodulation 20,46
  subsumption eq52 eq49


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
theorem Equation256_implies_Equation2680 (G : Type*) [Magma G] (h : Equation256 G) : Equation2680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).2.1 in 11
  have eq38 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := superpose eq33 eq10 -- backward demodulation 10,33
  subsumption eq38 eq9


@[equational_result]
theorem Equation2567_implies_Equation1035 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq14 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.1.2 in 9
  have eq22 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq18 eq12 -- backward demodulation 12,18
  have eq27 : sK0 ≠ sK0 := superpose eq22 eq13 -- superposition 13,22, 22 into 13, unify on (0).2 in 22 and (0).2 in 13
  subsumption eq27 rfl


@[equational_result]
theorem Equation2567_implies_Equation1258 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq20


@[equational_result]
theorem Equation2567_implies_Equation1478 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq27 -- forward demodulation 27,20
  subsumption eq30 eq26


@[equational_result]
theorem Equation2567_implies_Equation1701 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq26


@[equational_result]
theorem Equation2567_implies_Equation2161 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation2567_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq27 -- forward demodulation 27,20
  subsumption eq30 eq26


