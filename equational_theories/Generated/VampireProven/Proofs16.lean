import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation2725_implies_Equation4320 (G : Type*) [Magma G] (h : Equation2725 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq69 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq70 (X0 X1 X2 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq69 eq38 -- backward demodulation 38,69
  have eq244 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) := superpose eq9 eq70 -- superposition 70,9, 9 into 70, unify on (0).2 in 9 and (0).2.1 in 70
  have eq330 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq69 eq244 -- forward demodulation 244,69
  have eq937 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq330 eq330 -- superposition 330,330, 330 into 330, unify on (0).2 in 330 and (0).1 in 330
  have eq1022 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq330 eq10 -- superposition 10,330, 330 into 10, unify on (0).2 in 330 and (0).2 in 10
  subsumption eq1022 eq937


@[equational_result]
theorem Equation2725_implies_Equation1113 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3))) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq67 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq68 (X0 X1 X2 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq67 eq38 -- backward demodulation 38,67
  have eq294 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) := superpose eq9 eq68 -- superposition 68,9, 9 into 68, unify on (0).2 in 9 and (0).2.1 in 68
  have eq389 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := superpose eq67 eq294 -- forward demodulation 294,67
  have eq705 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X5 ◇ X5)))) = X0 := superpose eq37 eq35 -- superposition 35,37, 37 into 35, unify on (0).2 in 37 and (0).1.2 in 35
  have eq849 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ X1)) = X0 := superpose eq67 eq705 -- forward demodulation 705,67
  have eq976 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK0 ◇ (X0 ◇ X0)) ◇ sK1)) := superpose eq389 eq10 -- superposition 10,389, 389 into 10, unify on (0).2 in 389 and (0).2.2.1 in 10
  subsumption eq976 eq849


@[equational_result]
theorem Equation2725_implies_Equation2573 (G : Type*) [Magma G] (h : Equation2725 G) : Equation2573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq67 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq68 (X0 X1 X2 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq67 eq38 -- backward demodulation 38,67
  have eq294 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) := superpose eq9 eq68 -- superposition 68,9, 9 into 68, unify on (0).2 in 9 and (0).2.1 in 68
  have eq389 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq67 eq294 -- forward demodulation 294,67
  have eq913 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq389 eq389 -- superposition 389,389, 389 into 389, unify on (0).2 in 389 and (0).1 in 389
  have eq988 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) = X1 := superpose eq389 eq9 -- superposition 9,389, 389 into 9, unify on (0).2 in 389 and (0).1.1 in 9
  have eq1721 (X0 : G) : sK0 ≠ ((X0 ◇ ((sK2 ◇ sK0) ◇ X0)) ◇ sK2) := superpose eq913 eq10 -- superposition 10,913, 913 into 10, unify on (0).2 in 913 and (0).2.1 in 10
  subsumption eq1721 eq988


@[equational_result]
theorem Equation2725_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  have eq536 (X1 X2 : G) : sK0 ≠ ((sK1 ◇ (X1 ◇ X1)) ◇ ((sK0 ◇ sK1) ◇ (X2 ◇ X2))) := superpose eq37 eq59 -- superposition 59,37, 37 into 59, unify on (0).2 in 37 and (0).2 in 59
  subsumption eq536 eq11


@[equational_result]
theorem Equation2725_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2.2 in 11
  have eq50 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.2 in 9
  have eq225 : sK0 ≠ sK0 := superpose eq10 eq50 -- superposition 50,10, 10 into 50, unify on (0).2 in 10 and (0).2 in 50
  subsumption eq225 rfl


@[equational_result]
theorem Equation2725_implies_Equation4325 (G : Type*) [Magma G] (h : Equation2725 G) : Equation4325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq69 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq70 (X0 X1 X2 X5 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ (X5 ◇ X5))) := superpose eq69 eq38 -- backward demodulation 38,69
  have eq244 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) := superpose eq9 eq70 -- superposition 70,9, 9 into 70, unify on (0).2 in 9 and (0).2.1 in 70
  have eq330 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq69 eq244 -- forward demodulation 244,69
  have eq937 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ X3)) := superpose eq330 eq330 -- superposition 330,330, 330 into 330, unify on (0).2 in 330 and (0).1 in 330
  have eq1022 (X0 : G) : (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ (sK1 ◇ X0)) := superpose eq330 eq10 -- superposition 10,330, 330 into 10, unify on (0).2 in 330 and (0).2 in 10
  subsumption eq1022 eq937


@[equational_result]
theorem Equation2725_implies_Equation1086 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3))) = X2 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK0 ◇ (X0 ◇ X0)) ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.1.2 in 10
  have eq69 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  have eq540 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X5 ◇ X5)))) = X0 := superpose eq37 eq35 -- superposition 35,37, 37 into 35, unify on (0).2 in 37 and (0).1.2 in 35
  have eq666 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ X1)) = X0 := superpose eq69 eq540 -- forward demodulation 540,69
  have eq1299 : sK0 ≠ sK0 := superpose eq666 eq59 -- superposition 59,666, 666 into 59, unify on (0).2 in 666 and (0).2 in 59
  subsumption eq1299 rfl


@[equational_result]
theorem Equation2725_implies_Equation1861 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq24 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X0 := superpose eq21 eq19 -- backward demodulation 19,21
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.2 in 10
  have eq69 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq24 eq51 -- forward demodulation 51,24
  subsumption eq59 eq69


@[equational_result]
theorem Equation2725_implies_Equation1902 (G : Type*) [Magma G] (h : Equation2725 G) : Equation1902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq59 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  have eq536 (X1 X2 : G) : sK0 ≠ ((sK1 ◇ (X1 ◇ X1)) ◇ ((sK0 ◇ sK1) ◇ (X2 ◇ X2))) := superpose eq37 eq59 -- superposition 59,37, 37 into 59, unify on (0).2 in 37 and (0).2 in 59
  subsumption eq536 eq11


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
theorem Equation1695_implies_Equation680 (G : Type*) [Magma G] (h : Equation1695 G) : Equation680 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1.1 in 11
  have eq19 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq67 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1.2 in 22
  have eq105 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1 in 19
  have eq162 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose eq67 eq9 -- superposition 9,67, 67 into 9, unify on (0).2 in 67 and (0).1.1 in 9
  have eq170 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq105 eq162 -- forward demodulation 162,105
  have eq283 : sK0 ≠ sK0 := superpose eq170 eq10 -- superposition 10,170, 170 into 10, unify on (0).2 in 170 and (0).2 in 10
  subsumption eq283 rfl


@[equational_result]
theorem Equation1695_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1695 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.2.1.1 in 10
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq66 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq8 eq21 -- superposition 21,8, 8 into 21, unify on (0).2 in 8 and (0).1.2 in 21
  have eq99 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq11 eq18 -- superposition 18,11, 11 into 18, unify on (0).2 in 11 and (0).1 in 18
  have eq156 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq66 eq66 -- superposition 66,66, 66 into 66, unify on (0).2 in 66 and (0).1.1 in 66
  have eq157 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq66 eq21 -- superposition 21,66, 66 into 21, unify on (0).2 in 66 and (0).1.1 in 21
  have eq164 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq99 eq157 -- forward demodulation 157,99
  have eq165 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq8 eq164 -- forward demodulation 164,8
  have eq396 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq156 eq165 -- superposition 165,156, 156 into 165, unify on (0).2 in 156 and (0).1.2.2 in 165
  have eq547 : sK0 ≠ sK0 := superpose eq396 eq9 -- superposition 9,396, 396 into 9, unify on (0).2 in 396 and (0).2 in 9
  subsumption eq547 rfl


@[equational_result]
theorem Equation1932_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1932 G) : Equation1695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq23 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq44 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq23 eq12 -- superposition 12,23, 23 into 12, unify on (0).2 in 23 and (0).2.2 in 12
  have eq46 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq23 eq9 -- superposition 9,23, 23 into 9, unify on (0).2 in 23 and (0).1.1 in 9
  have eq98 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) = X0 := superpose eq46 eq9 -- superposition 9,46, 46 into 9, unify on (0).2 in 46 and (0).1.2 in 9
  have eq102 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq44 eq98 -- forward demodulation 98,44
  have eq116 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq23 eq102 -- superposition 102,23, 23 into 102, unify on (0).2 in 23 and (0).1.1.1 in 102
  have eq213 : sK0 ≠ sK0 := superpose eq116 eq10 -- superposition 10,116, 116 into 10, unify on (0).2 in 116 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation1932_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1932 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.1 in 10
  have eq22 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq43 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq22 eq11 -- superposition 11,22, 22 into 11, unify on (0).2 in 22 and (0).2.2 in 11
  have eq45 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq22 eq8 -- superposition 8,22, 22 into 8, unify on (0).2 in 22 and (0).1.1 in 8
  have eq97 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) = X0 := superpose eq45 eq8 -- superposition 8,45, 45 into 8, unify on (0).2 in 45 and (0).1.2 in 8
  have eq101 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq43 eq97 -- forward demodulation 97,43
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq22 eq101 -- superposition 101,22, 22 into 101, unify on (0).2 in 22 and (0).1.1.1 in 101
  have eq212 : sK0 ≠ sK0 := superpose eq115 eq9 -- superposition 9,115, 115 into 9, unify on (0).2 in 115 and (0).2 in 9
  subsumption eq212 rfl


@[equational_result]
theorem Equation1932_implies_Equation2847 (G : Type*) [Magma G] (h : Equation1932 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1.1 in 10
  have eq22 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq43 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq22 eq11 -- superposition 11,22, 22 into 11, unify on (0).2 in 22 and (0).2.2 in 11
  have eq45 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq22 eq8 -- superposition 8,22, 22 into 8, unify on (0).2 in 22 and (0).1.1 in 8
  have eq97 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) = X0 := superpose eq45 eq8 -- superposition 8,45, 45 into 8, unify on (0).2 in 45 and (0).1.2 in 8
  have eq101 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq43 eq97 -- forward demodulation 97,43
  have eq126 : sK0 ≠ sK0 := superpose eq101 eq9 -- superposition 9,101, 101 into 9, unify on (0).2 in 101 and (0).2 in 9
  subsumption eq126 rfl


@[equational_result]
theorem Equation1707_implies_Equation1977 (G : Type*) [Magma G] (h : Equation1707 G) : Equation1977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq20 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.1 in 11
  have eq24 (X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = ((X4 ◇ X2) ◇ X4) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2 in 11
  have eq25 (X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3))) = X4 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq24 eq12 -- superposition 12,24, 24 into 12, unify on (0).2 in 24 and (0).1.1 in 12
  have eq199 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) = X1 := superpose eq20 eq25 -- superposition 25,20, 20 into 25, unify on (0).2 in 20 and (0).1 in 25
  have eq202 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4))) := superpose eq25 eq20 -- superposition 20,25, 25 into 20, unify on (0).2 in 25 and (0).1.1 in 20
  have eq240 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X4)) = (((X3 ◇ X2) ◇ X3) ◇ (X5 ◇ (X0 ◇ X5))) := superpose eq11 eq35 -- superposition 35,11, 11 into 35, unify on (0).2 in 11 and (0).2.1 in 35
  have eq277 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ ((X1 ◇ X0) ◇ X5))) = ((X4 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X4) := superpose eq35 eq20 -- superposition 20,35, 35 into 20, unify on (0).2 in 35 and (0).1.1.2 in 20
  have eq287 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ ((X0 ◇ X2) ◇ X4))) := superpose eq35 eq20 -- superposition 20,35, 35 into 20, unify on (0).2 in 35 and (0).1.1 in 20
  have eq303 (X0 X1 X2 X4 : G) : (X2 ◇ X0) = (X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X4)) := superpose eq72 eq240 -- forward demodulation 240,72
  have eq304 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose eq303 eq202 -- backward demodulation 202,303
  have eq309 (X0 X1 X5 : G) : (X0 ◇ (X5 ◇ ((X1 ◇ X0) ◇ X5))) = X1 := superpose eq199 eq277 -- forward demodulation 277,199
  have eq336 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := superpose eq309 eq287 -- forward demodulation 287,309
  have eq596 (X0 : G) : sK0 ≠ ((X0 ◇ (sK2 ◇ X0)) ◇ (sK0 ◇ sK2)) := superpose eq304 eq10 -- superposition 10,304, 304 into 10, unify on (0).2 in 304 and (0).2.1 in 10
  subsumption eq596 eq336


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
theorem Equation1977_implies_Equation1707 (G : Type*) [Magma G] (h : Equation1977 G) : Equation1707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq36 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = (((X5 ◇ X2) ◇ X5) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) = (X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).1.2 in 36
  have eq71 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X3 ◇ X0) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).1.2 in 11
  have eq92 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq71 eq49 -- backward demodulation 49,71
  have eq103 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ (X5 ◇ (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ X5)))) = X4 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2.2.2.1 in 15
  have eq130 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ ((X3 ◇ X1) ◇ X3))) = X4 := superpose eq92 eq103 -- forward demodulation 103,92
  have eq147 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq130 eq130 -- superposition 130,130, 130 into 130, unify on (0).2 in 130 and (0).1.2 in 130
  have eq162 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) = X1 := superpose eq147 eq51 -- backward demodulation 51,147
  have eq315 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq11 eq162 -- superposition 162,11, 11 into 162, unify on (0).2 in 11 and (0).1.1 in 162
  have eq1133 : sK0 ≠ sK0 := superpose eq315 eq10 -- superposition 10,315, 315 into 10, unify on (0).2 in 315 and (0).2 in 10
  subsumption eq1133 rfl


@[equational_result]
theorem Equation1977_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1977 G) : Equation1684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq36 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = (((X5 ◇ X2) ◇ X5) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) = (X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).1.2 in 36
  have eq71 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X3 ◇ X0) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).1.2 in 11
  have eq92 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq71 eq49 -- backward demodulation 49,71
  have eq103 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ (X5 ◇ (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ X5)))) = X4 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2.2.2.1 in 15
  have eq130 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ ((X3 ◇ X1) ◇ X3))) = X4 := superpose eq92 eq103 -- forward demodulation 103,92
  have eq147 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq130 eq130 -- superposition 130,130, 130 into 130, unify on (0).2 in 130 and (0).1.2 in 130
  have eq162 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) = X1 := superpose eq147 eq51 -- backward demodulation 51,147
  have eq315 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq11 eq162 -- superposition 162,11, 11 into 162, unify on (0).2 in 11 and (0).1.1 in 162
  have eq1133 : sK0 ≠ sK0 := superpose eq315 eq10 -- superposition 10,315, 315 into 10, unify on (0).2 in 315 and (0).2 in 10
  subsumption eq1133 rfl


@[equational_result]
theorem Equation1977_implies_Equation2979 (G : Type*) [Magma G] (h : Equation1977 G) : Equation2979 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (((X3 ◇ X1) ◇ X3) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq36 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = (((X5 ◇ X2) ◇ X5) ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq71 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X3 ◇ X0) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq36 eq11 -- superposition 11,36, 36 into 11, unify on (0).2 in 36 and (0).1.2 in 11
  have eq92 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq71 eq49 -- backward demodulation 49,71
  have eq103 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X4 ◇ (X5 ◇ (((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) ◇ X5)))) = X4 := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2.2.2.1 in 15
  have eq130 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ ((X3 ◇ X1) ◇ X3))) = X4 := superpose eq92 eq103 -- forward demodulation 103,92
  have eq147 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq130 eq130 -- superposition 130,130, 130 into 130, unify on (0).2 in 130 and (0).1.2 in 130
  have eq249 (X0 : G) : sK0 ≠ (X0 ◇ (((sK2 ◇ sK0) ◇ sK2) ◇ X0)) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq249 eq147


@[equational_result]
theorem Equation1977_implies_Equation630 (G : Type*) [Magma G] (h : Equation1977 G) : Equation630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq36 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X2 ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq80 (X0 : G) : sK0 ≠ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose eq36 eq10 -- superposition 10,36, 36 into 10, unify on (0).2 in 36 and (0).2.2 in 10
  have eq139 (X0 : G) : sK0 ≠ ((X0 ◇ (sK0 ◇ X0)) ◇ (sK0 ◇ sK0)) := superpose eq15 eq80 -- superposition 80,15, 15 into 80, unify on (0).2 in 15 and (0).2 in 80
  subsumption eq139 eq9


@[equational_result]
theorem Equation2163_implies_Equation1483 (G : Type*) [Magma G] (h : Equation2163 G) : Equation1483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2163_implies_Equation3862 (G : Type*) [Magma G] (h : Equation2163 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X1))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.2 in 10
  have eq36 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).2 in 9
  subsumption eq36 rfl


@[equational_result]
theorem Equation2163_implies_Equation1427 (G : Type*) [Magma G] (h : Equation2163 G) : Equation1427 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


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
theorem Equation1483_implies_Equation2087 (G : Type*) [Magma G] (h : Equation1483 G) : Equation2087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1483_implies_Equation2125 (G : Type*) [Magma G] (h : Equation1483 G) : Equation2125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1483_implies_Equation3511 (G : Type*) [Magma G] (h : Equation1483 G) : Equation3511 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq36 rfl


@[equational_result]
theorem Equation1483_implies_Equation2051 (G : Type*) [Magma G] (h : Equation1483 G) : Equation2051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation1483_implies_Equation3456 (G : Type*) [Magma G] (h : Equation1483 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq16 (X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq35 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq35 rfl


@[equational_result]
theorem Equation457_implies_Equation644 (G : Type*) [Magma G] (h : Equation457 G) : Equation644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation457_implies_Equation2454 (G : Type*) [Magma G] (h : Equation457 G) : Equation2454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation457_implies_Equation461 (G : Type*) [Magma G] (h : Equation457 G) : Equation461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation457_implies_Equation449 (G : Type*) [Magma G] (h : Equation457 G) : Equation449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation57_implies_Equation457 (G : Type*) [Magma G] (h : Equation57 G) : Equation457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq11 : sK0 ≠ (sK0 ◇ sK1) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).2 in 11
  subsumption eq16 rfl


@[equational_result]
theorem Equation456_implies_Equation637 (G : Type*) [Magma G] (h : Equation456 G) : Equation637 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation456_implies_Equation57 (G : Type*) [Magma G] (h : Equation456 G) : Equation57 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq9 eq13 -- forward demodulation 13,9
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq14


@[equational_result]
theorem Equation853_implies_Equation456 (G : Type*) [Magma G] (h : Equation853 G) : Equation456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.2 in 11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2.1 in 14
  have eq43 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq37 -- forward demodulation 37,11
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) := superpose eq15 eq11 -- superposition 11,15, 15 into 11, unify on (0).2 in 15 and (0).1.2 in 11
  have eq995 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq43 eq99 -- superposition 99,43, 43 into 99, unify on (0).2 in 43 and (0).1.1.2 in 99
  have eq1065 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq995 -- forward demodulation 995,11
  have eq1152 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq1065 eq1065 -- superposition 1065,1065, 1065 into 1065, unify on (0).2 in 1065 and (0).2.2 in 1065
  have eq1211 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq1152 eq9 -- backward demodulation 9,1152
  have eq1254 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq1211 eq11 -- backward demodulation 11,1211
  have eq1315 : sK0 ≠ (sK0 ◇ sK1) := superpose eq1211 eq10 -- backward demodulation 10,1211
  subsumption eq1315 eq1254


@[equational_result]
theorem Equation435_implies_Equation2085 (G : Type*) [Magma G] (h : Equation435 G) : Equation2085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK3 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK3) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq19 : sK0 ≠ (sK0 ◇ sK3) := superpose eq13 eq18 -- forward demodulation 18,13
  subsumption eq19 eq13


@[equational_result]
theorem Equation435_implies_Equation853 (G : Type*) [Magma G] (h : Equation435 G) : Equation853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation461_implies_Equation435 (G : Type*) [Magma G] (h : Equation461 G) : Equation435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation461_implies_Equation460 (G : Type*) [Magma G] (h : Equation461 G) : Equation460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation461_implies_Equation3070 (G : Type*) [Magma G] (h : Equation461 G) : Equation3070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq9 -- backward demodulation 9,14
  have eq16 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq19 : sK0 ≠ (sK0 ◇ sK2) := superpose eq15 eq18 -- forward demodulation 18,15
  subsumption eq19 eq15


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
theorem Equation1487_implies_Equation2124 (G : Type*) [Magma G] (h : Equation1487 G) : Equation2124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
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
theorem Equation1487_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1487 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X4 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq25 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation2164_implies_Equation1487 (G : Type*) [Magma G] (h : Equation2164 G) : Equation1487 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2164_implies_Equation1485 (G : Type*) [Magma G] (h : Equation2164 G) : Equation1485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2164_implies_Equation167 (G : Type*) [Magma G] (h : Equation2164 G) : Equation167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2164_implies_Equation168 (G : Type*) [Magma G] (h : Equation2164 G) : Equation168 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3160_implies_Equation2701 (G : Type*) [Magma G] (h : Equation3160 G) : Equation2701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq26 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq14 eq19 -- superposition 19,14, 14 into 19, unify on (0).2 in 14 and (0).2.1 in 19
  subsumption eq26 eq14


@[equational_result]
theorem Equation671_implies_Equation673 (G : Type*) [Magma G] (h : Equation671 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation1148_implies_Equation1367 (G : Type*) [Magma G] (h : Equation1148 G) : Equation1367 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X2 X3 : G) : X2 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.1 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation69_implies_Equation573 (G : Type*) [Magma G] (h : Equation69 G) : Equation573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 : sK0 ≠ (sK1 ◇ sK2) := superpose eq9 eq10 -- forward demodulation 10,9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 : G) : X1 = X2 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq34 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.1 in 11
  subsumption eq34 eq16


@[equational_result]
theorem Equation2110_implies_Equation3127 (G : Type*) [Magma G] (h : Equation2110 G) : Equation3127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X4)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X1 X4 : G) : X1 = X4 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq38 (X0 : G) : sK0 ≠ (((X0 ◇ sK2) ◇ sK1) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.1.1 in 10
  subsumption eq38 eq33


@[equational_result]
theorem Equation776_implies_Equation792 (G : Type*) [Magma G] (h : Equation776 G) : Equation792 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq24 (X3 X4 : G) : X3 = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq81 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.2.2 in 10
  subsumption eq81 eq24


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
theorem Equation173_implies_Equation1351 (G : Type*) [Magma G] (h : Equation173 G) : Equation1351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq14 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ X4) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq20 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq14 eq12 -- backward demodulation 12,14
  have eq21 (X1 X3 : G) : X1 = X3 := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1 in 20
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq27 eq21


@[equational_result]
theorem Equation3114_implies_Equation890 (G : Type*) [Magma G] (h : Equation3114 G) : Equation890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq19 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq17 -- forward demodulation 17,12
  subsumption eq18 eq19


@[equational_result]
theorem Equation2092_implies_Equation3141 (G : Type*) [Magma G] (h : Equation2092 G) : Equation3141 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq24 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1.1 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq20 eq27 -- forward demodulation 27,20
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq29 eq12 -- backward demodulation 12,29
  have eq39 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2.2 in 30
  have eq48 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X3 := superpose eq19 eq39 -- forward demodulation 39,19
  have eq51 (X1 X3 : G) : (((X1 ◇ X3) ◇ X3) ◇ X1) = X3 := superpose eq48 eq13 -- backward demodulation 13,48
  have eq60 : sK0 ≠ (sK0 ◇ sK2) := superpose eq48 eq24 -- backward demodulation 24,48
  have eq63 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq48 eq51 -- forward demodulation 51,48
  subsumption eq60 eq63


@[equational_result]
theorem Equation471_implies_Equation472 (G : Type*) [Magma G] (h : Equation471 G) : Equation472 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2 in 10
  subsumption eq19 eq17


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
theorem Equation708_implies_Equation1976 (G : Type*) [Magma G] (h : Equation708 G) : Equation1976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq16


@[equational_result]
theorem Equation693_implies_Equation927 (G : Type*) [Magma G] (h : Equation693 G) : Equation927 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 X5 : G) : (X1 ◇ (X5 ◇ X2)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq20 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ sK0) := superpose eq20 eq16 -- superposition 16,20, 20 into 16, unify on (0).2 in 20 and (0).2.1 in 16
  subsumption eq23 eq20


@[equational_result]
theorem Equation685_implies_Equation1087 (G : Type*) [Magma G] (h : Equation685 G) : Equation1087 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X2 X5 : G) : (X0 ◇ (X5 ◇ X2)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation724_implies_Equation2365 (G : Type*) [Magma G] (h : Equation724 G) : Equation2365 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq24 (X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X3)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq32 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X4 ◇ X0) := superpose eq24 eq13 -- backward demodulation 13,24
  have eq73 (X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = X2 := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq107 (X0 X1 : G) : sK0 ≠ (X0 ◇ (X1 ◇ X0)) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq107 eq73


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
theorem Equation890_implies_Equation745 (G : Type*) [Magma G] (h : Equation890 G) : Equation745 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq35 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK2)) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq42 (X2 X3 : G) : X2 = X3 := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1 in 17
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq35 -- superposition 35,42, 42 into 35, unify on (0).2 in 42 and (0).2 in 35
  subsumption eq103 eq42


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
theorem Equation67_implies_Equation3144 (G : Type*) [Magma G] (h : Equation67 G) : Equation3144 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq18 (X0 : G) : sK0 ≠ (((X0 ◇ sK0) ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1.1 in 10
  subsumption eq18 eq14


@[equational_result]
theorem Equation908_implies_Equation945 (G : Type*) [Magma G] (h : Equation908 G) : Equation945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq37 (X1 X3 : G) : X1 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq51 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq51 eq37


@[equational_result]
theorem Equation2775_implies_Equation2382 (G : Type*) [Magma G] (h : Equation2775 G) : Equation2382 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (((X0 ◇ X3) ◇ X2) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq26 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq29 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X2 ◇ X0) ◇ X4) ◇ (((X0 ◇ X3) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq74 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := superpose eq12 eq26 -- superposition 26,12, 12 into 26, unify on (0).2 in 12 and (0).1.2 in 26
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq74 eq29 -- backward demodulation 29,74
  have eq99 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq9 eq90 -- superposition 90,9, 9 into 90, unify on (0).2 in 9 and (0).2.2 in 90
  have eq140 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq26 eq99 -- superposition 99,26, 26 into 99, unify on (0).2 in 26 and (0).1 in 99
  have eq178 (X0 : G) : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := superpose eq99 eq10 -- superposition 10,99, 99 into 10, unify on (0).2 in 99 and (0).2 in 10
  subsumption eq178 eq140


@[equational_result]
theorem Equation886_implies_Equation3177 (G : Type*) [Magma G] (h : Equation886 G) : Equation3177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) = ((X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X5 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))))))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.1 in 11
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X2))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X5 ◇ (X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)))))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq36 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq31 eq18 -- backward demodulation 18,31
  have eq38 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose eq31 eq11 -- backward demodulation 11,31
  have eq41 (X0 X1 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = ((X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X5 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1)))))))) := superpose eq31 eq14 -- backward demodulation 14,31
  have eq51 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq30 eq41 -- forward demodulation 41,30
  have eq53 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq51 eq38 -- backward demodulation 38,51
  have eq58 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq31 eq33 -- forward demodulation 33,31
  have eq59 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) := superpose eq31 eq58 -- forward demodulation 58,31
  have eq60 (X0 X1 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq31 eq59 -- forward demodulation 59,31
  have eq72 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq53 eq31 -- superposition 31,53, 53 into 31, unify on (0).2 in 53 and (0).2 in 31
  have eq84 (X0 X1 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ X1) := superpose eq72 eq60 -- backward demodulation 60,72
  have eq85 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq72 eq36 -- backward demodulation 36,72
  have eq87 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = X3 := superpose eq85 eq28 -- backward demodulation 28,85
  have eq108 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = ((X3 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X1) := superpose eq85 eq84 -- backward demodulation 84,85
  have eq109 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := superpose eq85 eq10 -- backward demodulation 10,85
  have eq112 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X3 := superpose eq85 eq87 -- forward demodulation 87,85
  have eq113 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq85 eq112 -- forward demodulation 112,85
  have eq144 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq113 eq108 -- forward demodulation 108,113
  have eq145 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq85 eq144 -- forward demodulation 144,85
  subsumption eq109 eq145


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
theorem Equation995_implies_Equation708 (G : Type*) [Magma G] (h : Equation995 G) : Equation708 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X4))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ X1)) ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq42 (X0 X1 X2 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq42 eq17


@[equational_result]
theorem Equation944_implies_Equation1765 (G : Type*) [Magma G] (h : Equation944 G) : Equation1765 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = (X3 ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1.2 in 13
  have eq37 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = (X4 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq49 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq13 eq34 -- superposition 34,13, 13 into 34, unify on (0).2 in 13 and (0).2 in 34
  have eq79 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq49 eq33 -- backward demodulation 33,49
  have eq81 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq49 eq79 -- forward demodulation 79,49
  have eq85 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) = (X5 ◇ (((X3 ◇ X2) ◇ X1) ◇ ((X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) ◇ X5))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq133 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X1 := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1.1 in 81
  have eq161 (X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) = X1 := superpose eq133 eq85 -- backward demodulation 85,133
  have eq162 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = (X4 ◇ X1) := superpose eq161 eq37 -- backward demodulation 37,161
  have eq178 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq81 eq162 -- superposition 162,81, 81 into 162, unify on (0).2 in 81 and (0).1 in 162
  have eq204 (X0 : G) : sK0 ≠ (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := superpose eq162 eq10 -- superposition 10,162, 162 into 10, unify on (0).2 in 162 and (0).2 in 10
  subsumption eq204 eq178


@[equational_result]
theorem Equation1087_implies_Equation944 (G : Type*) [Magma G] (h : Equation1087 G) : Equation944 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (sK1 ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq19 eq13


@[equational_result]
theorem Equation876_implies_Equation2984 (G : Type*) [Magma G] (h : Equation876 G) : Equation2984 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq16 (X1 X2 : G) : X1 = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq29 (X0 : G) : sK0 ≠ (X0 ◇ sK3) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.1 in 21
  subsumption eq29 eq16


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
theorem Equation705_implies_Equation2901 (G : Type*) [Magma G] (h : Equation705 G) : Equation2901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1 in 11
  have eq18 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.1 in 10
  subsumption eq18 eq16


@[equational_result]
theorem Equation3026_implies_Equation705 (G : Type*) [Magma G] (h : Equation3026 G) : Equation705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X1 X4 X5 : G) : ((X4 ◇ X5) ◇ X1) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq19 (X2 X3 : G) : X2 = X3 := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq22 (X0 : G) : sK0 ≠ (X0 ◇ (X0 ◇ sK0)) := superpose eq19 eq16 -- superposition 16,19, 19 into 16, unify on (0).2 in 19 and (0).2.1 in 16
  subsumption eq22 eq19


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
theorem Equation961_implies_Equation3026 (G : Type*) [Magma G] (h : Equation961 G) : Equation3026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) = (((X4 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) ◇ X3) ◇ ((X5 ◇ ((X4 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (((X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2)) ◇ X1) ◇ ((X5 ◇ ((X4 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.2 in 12
  have eq35 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.1.2 in 17
  have eq40 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1 in 12
  have eq42 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2)))) = X3 := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2.1 in 9
  have eq69 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq9 eq40 -- superposition 40,9, 9 into 40, unify on (0).2 in 9 and (0).1.1.1 in 40
  have eq87 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq40 eq9 -- superposition 9,40, 40 into 9, unify on (0).2 in 40 and (0).1.2.2 in 9
  have eq141 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq42 -- superposition 42,9, 9 into 42, unify on (0).2 in 9 and (0).1.2 in 42
  have eq147 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X1) := superpose eq17 eq42 -- superposition 42,17, 17 into 42, unify on (0).2 in 17 and (0).1.2 in 42
  have eq174 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ ((X5 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq141 eq25 -- backward demodulation 25,141
  have eq179 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK2) := superpose eq141 eq10 -- backward demodulation 10,141
  have eq187 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = ((X1 ◇ X1) ◇ ((X5 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq147 eq174 -- backward demodulation 174,147
  have eq195 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq147 eq179 -- backward demodulation 179,147
  have eq197 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = (X1 ◇ X1) := superpose eq147 eq187 -- forward demodulation 187,147
  have eq203 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq197 eq35 -- backward demodulation 35,197
  have eq212 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (X0 ◇ X0) := superpose eq147 eq203 -- forward demodulation 203,147
  have eq213 (X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X1 ◇ X2)) = X3 := superpose eq212 eq40 -- backward demodulation 40,212
  have eq228 (X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = (((X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3) ◇ ((X5 ◇ ((X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3)) ◇ (X1 ◇ X1))) := superpose eq212 eq24 -- backward demodulation 24,212
  have eq260 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq213 eq69 -- backward demodulation 69,213
  have eq262 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := superpose eq260 eq87 -- backward demodulation 87,260
  have eq275 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq262 eq228 -- forward demodulation 228,262
  have eq277 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq275 eq42 -- backward demodulation 42,275
  have eq283 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq277 eq141 -- backward demodulation 141,277
  have eq291 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = X3 := superpose eq283 eq275 -- backward demodulation 275,283
  have eq305 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq283 eq291 -- forward demodulation 291,283
  subsumption eq195 eq305


@[equational_result]
theorem Equation683_implies_Equation2941 (G : Type*) [Magma G] (h : Equation683 G) : Equation2941 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq23 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq23 eq16


@[equational_result]
theorem Equation3228_implies_Equation2938 (G : Type*) [Magma G] (h : Equation3228 G) : Equation2938 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq14 -- superposition 14,17, 17 into 14, unify on (0).2 in 17 and (0).2 in 14
  subsumption eq28 eq17


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
theorem Equation1959_implies_Equation1926 (G : Type*) [Magma G] (h : Equation1959 G) : Equation1926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X1) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq18 eq28 -- forward demodulation 28,18
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1) = X0 := superpose eq37 eq20 -- backward demodulation 20,37
  have eq49 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) := superpose eq37 eq10 -- backward demodulation 10,37
  have eq53 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = X0 := superpose eq37 eq41 -- forward demodulation 41,37
  have eq54 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq37 eq53 -- forward demodulation 53,37
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq54 -- forward demodulation 54,18
  have eq57 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq55 eq11 -- backward demodulation 11,55
  have eq64 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq55 eq57 -- forward demodulation 57,55
  have eq65 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq55 eq64 -- forward demodulation 64,55
  have eq76 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq55 eq49 -- forward demodulation 49,55
  have eq77 : sK0 ≠ (sK1 ◇ sK1) := superpose eq55 eq76 -- forward demodulation 76,55
  have eq88 : sK0 ≠ sK1 := superpose eq65 eq77 -- superposition 77,65, 65 into 77, unify on (0).2 in 65 and (0).2 in 77
  have eq89 (X0 X1 : G) : X0 = X1 := superpose eq65 eq55 -- superposition 55,65, 65 into 55, unify on (0).2 in 65 and (0).1 in 55
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq88 -- superposition 88,89, 89 into 88, unify on (0).2 in 89 and (0).2 in 88
  subsumption eq92 eq89


@[equational_result]
theorem Equation691_implies_Equation1976 (G : Type*) [Magma G] (h : Equation691 G) : Equation1976 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1.1 in 12
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1.1 in 17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq17 eq9 -- superposition 9,17, 17 into 9, unify on (0).2 in 17 and (0).1.2 in 9
  have eq54 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq9 eq40 -- forward demodulation 40,9
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq54 eq31 -- backward demodulation 31,54
  have eq66 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq52 -- forward demodulation 52,9
  have eq68 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq66 eq62 -- backward demodulation 62,66
  have eq70 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq66 eq15 -- backward demodulation 15,66
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq70 eq68 -- backward demodulation 68,70
  have eq72 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq71 eq9 -- backward demodulation 9,71
  have eq75 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq71 eq54 -- backward demodulation 54,71
  have eq81 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X2 := superpose eq75 eq19 -- backward demodulation 19,75
  have eq82 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1.2 in 81
  have eq90 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq84 eq72 -- backward demodulation 72,84
  have eq101 (X2 X3 : G) : X2 = X3 := superpose eq90 eq90 -- superposition 90,90, 90 into 90, unify on (0).2 in 90 and (0).1 in 90
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq82 -- superposition 82,90, 90 into 82, unify on (0).2 in 90 and (0).2 in 82
  subsumption eq106 eq101


@[equational_result]
theorem Equation83_implies_Equation678 (G : Type*) [Magma G] (h : Equation83 G) : Equation678 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq23 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (sK0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq23 eq16


@[equational_result]
theorem Equation475_implies_Equation750 (G : Type*) [Magma G] (h : Equation475 G) : Equation750 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X1 X2 : G) : X1 = X2 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ ((X0 ◇ X0) ◇ sK2))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.2.1 in 10
  subsumption eq17 eq15


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
theorem Equation1928_implies_Equation3009 (G : Type*) [Magma G] (h : Equation1928 G) : Equation3009 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq24 (X1 X3 : G) : X1 = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq36 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq18 eq23 -- superposition 23,18, 18 into 23, unify on (0).2 in 18 and (0).2.1 in 23
  subsumption eq36 eq24


@[equational_result]
theorem Equation3141_implies_Equation674 (G : Type*) [Magma G] (h : Equation3141 G) : Equation674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq13 -- forward demodulation 13,12
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq19 (X0 X1 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq19 eq17


@[equational_result]
theorem Equation745_implies_Equation2704 (G : Type*) [Magma G] (h : Equation745 G) : Equation2704 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq27 eq18


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
theorem Equation687_implies_Equation1297 (G : Type*) [Magma G] (h : Equation687 G) : Equation1297 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq15 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1.1 in 13
  have eq35 (X0 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X0)) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1.1 in 13
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq42 (X0 X3 : G) : (X3 ◇ X0) = (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (((X2 ◇ X1) ◇ X0) ◇ X1) := superpose eq14 eq39 -- forward demodulation 39,14
  have eq53 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK0))) := superpose eq52 eq10 -- backward demodulation 10,52
  have eq54 (X0 X3 : G) : (X0 ◇ X3) = (X3 ◇ X0) := superpose eq35 eq42 -- forward demodulation 42,35
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = X0 := superpose eq54 eq13 -- backward demodulation 13,54
  have eq59 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := superpose eq54 eq53 -- backward demodulation 53,54
  have eq88 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq9 eq56 -- superposition 56,9, 9 into 56, unify on (0).2 in 9 and (0).1.1 in 56
  have eq107 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq88 eq9 -- backward demodulation 9,88
  have eq108 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq88 eq11 -- backward demodulation 11,88
  have eq130 : sK0 ≠ (sK1 ◇ sK0) := superpose eq108 eq59 -- backward demodulation 59,108
  have eq156 (X0 X1 : G) : X0 = X1 := superpose eq15 eq107 -- superposition 107,15, 15 into 107, unify on (0).2 in 15 and (0).1 in 107
  have eq167 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq107 eq130 -- superposition 130,107, 107 into 130, unify on (0).2 in 107 and (0).2 in 130
  subsumption eq167 eq156


@[equational_result]
theorem Equation1282_implies_Equation521 (G : Type*) [Magma G] (h : Equation1282 G) : Equation521 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X1 X3 : G) : X1 = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq26 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2 in 10
  subsumption eq26 eq16


@[equational_result]
theorem Equation675_implies_Equation2938 (G : Type*) [Magma G] (h : Equation675 G) : Equation2938 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X5))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X2 X5 : G) : (X5 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq16 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq16 eq14


@[equational_result]
theorem Equation2984_implies_Equation1554 (G : Type*) [Magma G] (h : Equation2984 G) : Equation1554 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq13 (X2 X3 X4 : G) : (X3 ◇ X4) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X2 X4 : G) : X2 = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq20 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ X0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq20 eq14


@[equational_result]
theorem Equation678_implies_Equation1696 (G : Type*) [Magma G] (h : Equation678 G) : Equation1696 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1 in 12
  have eq19 : sK0 ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq19 eq18


@[equational_result]
theorem Equation884_implies_Equation758 (G : Type*) [Magma G] (h : Equation884 G) : Equation758 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq35 (X1 X3 : G) : X1 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq53 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.2 in 10
  subsumption eq53 eq35


@[equational_result]
theorem Equation2806_implies_Equation1351 (G : Type*) [Magma G] (h : Equation2806 G) : Equation1351 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK0) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq35 (X2 X3 : G) : X2 = X3 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq48 eq35


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
theorem Equation472_implies_Equation741 (G : Type*) [Magma G] (h : Equation472 G) : Equation741 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq16 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq14 eq12 -- backward demodulation 12,14
  subsumption eq16 eq17


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
theorem Equation3181_implies_Equation673 (G : Type*) [Magma G] (h : Equation3181 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq77 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq64 eq9 -- backward demodulation 9,64
  have eq114 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq64 eq19 -- backward demodulation 19,64
  have eq117 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq77 eq64 -- backward demodulation 64,77
  subsumption eq114 eq117


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
theorem Equation498_implies_Equation1959 (G : Type*) [Magma G] (h : Equation498 G) : Equation1959 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X2 X3 : G) : X2 = X3 := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 eq15


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
theorem Equation1147_implies_Equation2974 (G : Type*) [Magma G] (h : Equation1147 G) : Equation2974 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq40 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq48 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq40 eq10 -- backward demodulation 10,40
  have eq52 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq12 eq40 -- superposition 40,12, 12 into 40, unify on (0).2 in 12 and (0).2 in 40
  have eq73 : sK0 ≠ (sK1 ◇ sK1) := superpose eq40 eq48 -- superposition 48,40, 40 into 48, unify on (0).2 in 40 and (0).2 in 48
  subsumption eq73 eq52


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
theorem Equation945_implies_Equation83 (G : Type*) [Magma G] (h : Equation945 G) : Equation83 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq25 eq23


@[equational_result]
theorem Equation480_implies_Equation3196 (G : Type*) [Magma G] (h : Equation480 G) : Equation3196 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK1) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  have eq29 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ sK3) := superpose eq14 eq16 -- superposition 16,14, 14 into 16, unify on (0).2 in 14 and (0).2.1 in 16
  have eq30 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq19 eq17 -- backward demodulation 17,19
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = X3 := superpose eq19 eq30 -- forward demodulation 30,19
  subsumption eq29 eq34


@[equational_result]
theorem Equation480_implies_Equation1692 (G : Type*) [Magma G] (h : Equation480 G) : Equation1692 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq20 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2 in 14
  have eq29 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ (sK1 ◇ sK1)) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.1 in 18
  have eq31 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq20 eq17 -- backward demodulation 17,20
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = X3 := superpose eq20 eq31 -- forward demodulation 31,20
  subsumption eq29 eq35


@[equational_result]
theorem Equation3151_implies_Equation908 (G : Type*) [Magma G] (h : Equation3151 G) : Equation908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1.1 in 9
  have eq17 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ X4) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq9 -- backward demodulation 9,17
  have eq27 : sK0 ≠ (sK1 ◇ sK0) := superpose eq17 eq10 -- backward demodulation 10,17
  subsumption eq27 eq26


@[equational_result]
theorem Equation913_implies_Equation3151 (G : Type*) [Magma G] (h : Equation913 G) : Equation3151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 (X0 X1 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq26 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.1 in 9
  have eq34 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq26 eq25 -- backward demodulation 25,26
  have eq45 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq58 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1))) = X3 := superpose eq45 eq12 -- backward demodulation 12,45
  have eq77 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq26 -- superposition 26,11, 11 into 26, unify on (0).2 in 11 and (0).1.1 in 26
  have eq93 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq77 eq30 -- backward demodulation 30,77
  have eq113 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (((X4 ◇ (X2 ◇ X0)) ◇ (X5 ◇ X4)) ◇ (((X4 ◇ (X2 ◇ X0)) ◇ (X5 ◇ X4)) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0))))) := superpose eq11 eq58 -- superposition 58,11, 11 into 58, unify on (0).2 in 11 and (0).1.2.2 in 58
  have eq152 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq93 eq26 -- superposition 26,93, 93 into 26, unify on (0).2 in 93 and (0).1.1.2 in 26
  have eq163 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK2) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2.1 in 10
  have eq183 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq26 eq34 -- superposition 34,26, 26 into 34, unify on (0).2 in 26 and (0).1.2.2.2 in 34
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq183 eq113 -- backward demodulation 113,183
  have eq214 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X1 := superpose eq209 eq152 -- backward demodulation 152,209
  have eq218 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq209 eq163 -- backward demodulation 163,209
  have eq294 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq209 eq214 -- forward demodulation 214,209
  have eq295 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq209 eq294 -- forward demodulation 294,209
  subsumption eq218 eq295


@[equational_result]
theorem Equation1077_implies_Equation2099 (G : Type*) [Magma G] (h : Equation1077 G) : Equation2099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X1 X3 : G) : X1 = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq19 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK2)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq19 eq13


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
theorem Equation2166_implies_Equation876 (G : Type*) [Magma G] (h : Equation2166 G) : Equation876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq37 (X1 X2 : G) : X1 = X2 := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1 in 16
  have eq49 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq49 eq37


@[equational_result]
theorem Equation2109_implies_Equation2717 (G : Type*) [Magma G] (h : Equation2109 G) : Equation2717 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq32 : sK0 ≠ (sK2 ◇ sK1) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq49 (X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq61 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) = X4 := superpose eq13 eq23 -- superposition 23,13, 13 into 23, unify on (0).2 in 13 and (0).1.1 in 23
  have eq78 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq61 eq21 -- backward demodulation 21,61
  have eq81 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq23 eq78 -- forward demodulation 78,23
  have eq85 (X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq81 eq49 -- backward demodulation 49,81
  have eq110 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq81 eq85 -- forward demodulation 85,81
  have eq112 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq110 eq23 -- backward demodulation 23,110
  have eq118 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq110 eq112 -- forward demodulation 112,110
  have eq121 (X0 X1 : G) : X0 = X1 := superpose eq110 eq118 -- superposition 118,110, 110 into 118, unify on (0).2 in 110 and (0).1 in 118
  have eq126 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq118 eq32 -- superposition 32,118, 118 into 32, unify on (0).2 in 118 and (0).2 in 32
  subsumption eq126 eq121


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
theorem Equation1926_implies_Equation173 (G : Type*) [Magma G] (h : Equation1926 G) : Equation173 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X1) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq40 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X4)) ◇ X1) = X2 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq46 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq18 eq40 -- forward demodulation 40,18
  have eq48 (X1 X2 : G) : X1 = X2 := superpose eq9 eq46 -- superposition 46,9, 9 into 46, unify on (0).2 in 9 and (0).1 in 46
  have eq68 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq68 eq48


@[equational_result]
theorem Equation1994_implies_Equation2922 (G : Type*) [Magma G] (h : Equation1994 G) : Equation2922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK3) := mod_symm nh
  have eq11 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq14 eq13 -- backward demodulation 13,14
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1.2 in 17
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq14 eq17 -- superposition 17,14, 14 into 17, unify on (0).2 in 14 and (0).1 in 17
  have eq28 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK3) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq28 -- superposition 28,24, 24 into 28, unify on (0).2 in 24 and (0).2 in 28
  subsumption eq35 eq24


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
theorem Equation668_implies_Equation496 (G : Type*) [Magma G] (h : Equation668 G) : Equation496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 : sK0 ≠ (sK1 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X1 X3 : G) : X1 = X3 := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2 in 16
  subsumption eq21 eq18


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
theorem Equation2772_implies_Equation995 (G : Type*) [Magma G] (h : Equation2772 G) : Equation995 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : X1 = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq20 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq20 eq14


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
theorem Equation490_implies_Equation589 (G : Type*) [Magma G] (h : Equation490 G) : Equation589 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X1))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 : sK0 ≠ (sK1 ◇ sK3) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq15 eq14


@[equational_result]
theorem Equation465_implies_Equation2921 (G : Type*) [Magma G] (h : Equation465 G) : Equation2921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq9 -- backward demodulation 9,11
  have eq15 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq16 eq17


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
theorem Equation3135_implies_Equation3228 (G : Type*) [Magma G] (h : Equation3135 G) : Equation3228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK3) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X2 X3 : G) : X2 = X3 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1 in 13
  have eq26 (X0 X1 : G) : sK0 ≠ ((X0 ◇ (X1 ◇ X0)) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq26 eq18


