import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

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
theorem Equation1789_implies_Equation1163 (G : Type*) [Magma G] (h : Equation1789 G) : Equation1163 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
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
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq111 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := superpose eq110 eq10 -- backward demodulation 10,110
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq107 eq110 -- backward demodulation 110,107
  have eq117 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq107 eq111 -- backward demodulation 111,107
  subsumption eq117 eq114


@[equational_result]
theorem Equation1789_implies_Equation579 (G : Type*) [Magma G] (h : Equation1789 G) : Equation579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
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
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq111 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := superpose eq110 eq10 -- backward demodulation 10,110
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq107 eq110 -- backward demodulation 110,107
  have eq117 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq107 eq111 -- backward demodulation 111,107
  subsumption eq117 eq114


@[equational_result]
theorem Equation1750_implies_Equation1789 (G : Type*) [Magma G] (h : Equation1750 G) : Equation1789 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq30 rfl


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
theorem Equation2212_implies_Equation1772 (G : Type*) [Magma G] (h : Equation2212 G) : Equation1772 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X5 ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X3 X4 : G) : (X3 ◇ (X4 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq11


@[equational_result]
theorem Equation2178_implies_Equation2212 (G : Type*) [Magma G] (h : Equation2178 G) : Equation2212 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation2178_implies_Equation1129 (G : Type*) [Magma G] (h : Equation2178 G) : Equation1129 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq19 eq12


@[equational_result]
theorem Equation2178_implies_Equation1709 (G : Type*) [Magma G] (h : Equation2178 G) : Equation1709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq19 eq12


@[equational_result]
theorem Equation1900_implies_Equation1088 (G : Type*) [Magma G] (h : Equation1900 G) : Equation1088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X1) = ((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1.2 in 12
  have eq81 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq115 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq12 eq81 -- superposition 81,12, 12 into 81, unify on (0).2 in 12 and (0).1.2 in 81
  have eq172 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq115 eq9 -- backward demodulation 9,115
  have eq207 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq172 eq10 -- backward demodulation 10,172
  subsumption eq207 eq172


@[equational_result]
theorem Equation1759_implies_Equation566 (G : Type*) [Magma G] (h : Equation1759 G) : Equation566 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq16 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq21 : sK0 ≠ (sK1 ◇ (sK3 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq30 : sK0 ≠ sK0 := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2 in 21
  subsumption eq30 rfl


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
theorem Equation1941_implies_Equation130 (G : Type*) [Magma G] (h : Equation1941 G) : Equation130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq17 (X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).1.2 in 17
  have eq32 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq32 eq17


@[equational_result]
theorem Equation114_implies_Equation1941 (G : Type*) [Magma G] (h : Equation114 G) : Equation1941 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq22 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq22 eq18


@[equational_result]
theorem Equation1927_implies_Equation593 (G : Type*) [Magma G] (h : Equation1927 G) : Equation593 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X1) = ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1.2 in 13
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq14 eq23 -- superposition 23,14, 14 into 23, unify on (0).2 in 14 and (0).2 in 23
  have eq58 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := superpose eq50 eq10 -- backward demodulation 10,50
  have eq61 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq23 eq34 -- superposition 34,23, 23 into 34, unify on (0).2 in 23 and (0).1.2 in 34
  have eq67 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq14 eq61 -- forward demodulation 61,14
  have eq68 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq67 eq58 -- backward demodulation 58,67
  have eq69 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq50 eq68 -- forward demodulation 68,50
  subsumption eq69 eq67


@[equational_result]
theorem Equation1927_implies_Equation1975 (G : Type*) [Magma G] (h : Equation1927 G) : Equation1975 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq19 -- superposition 19,12, 12 into 19, unify on (0).2 in 12 and (0).2.2 in 19
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq23 -- superposition 23,12, 12 into 23, unify on (0).2 in 12 and (0).1.2 in 23
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq19 eq23 -- superposition 23,19, 19 into 23, unify on (0).2 in 19 and (0).1.2 in 23
  have eq59 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq35 eq23 -- superposition 23,35, 35 into 23, unify on (0).2 in 35 and (0).1.2 in 23
  have eq65 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq59 eq41 -- backward demodulation 41,59
  have eq82 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq40 eq14 -- superposition 14,40, 40 into 14, unify on (0).2 in 40 and (0).2.2 in 14
  subsumption eq82 eq65


@[equational_result]
theorem Equation1927_implies_Equation3300 (G : Type*) [Magma G] (h : Equation1927 G) : Equation3300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X1) = ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1.2 in 13
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq14 eq23 -- superposition 23,14, 14 into 23, unify on (0).2 in 14 and (0).2 in 23
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).2 in 23
  have eq58 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq50 eq10 -- backward demodulation 10,50
  have eq61 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq23 eq34 -- superposition 34,23, 23 into 34, unify on (0).2 in 23 and (0).1.2 in 34
  have eq67 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq14 eq61 -- forward demodulation 61,14
  have eq68 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq67 eq58 -- backward demodulation 58,67
  subsumption eq68 eq51


@[equational_result]
theorem Equation1927_implies_Equation1801 (G : Type*) [Magma G] (h : Equation1927 G) : Equation1801 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X1) = ((X3 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).2.1.2 in 13
  have eq30 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq23 eq10 -- backward demodulation 10,23
  have eq31 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq14 eq30 -- forward demodulation 30,14
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq87 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq14 eq23 -- superposition 23,14, 14 into 23, unify on (0).2 in 14 and (0).2 in 23
  have eq98 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq23 eq61 -- superposition 61,23, 23 into 61, unify on (0).2 in 23 and (0).1.2 in 61
  have eq137 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq87 eq31 -- superposition 31,87, 87 into 31, unify on (0).2 in 87 and (0).2 in 31
  subsumption eq137 eq98


@[equational_result]
theorem Equation1927_implies_Equation2066 (G : Type*) [Magma G] (h : Equation1927 G) : Equation2066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq23 -- superposition 23,12, 12 into 23, unify on (0).2 in 12 and (0).1.2 in 23
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq14 eq23 -- superposition 23,14, 14 into 23, unify on (0).2 in 14 and (0).1.2 in 23
  have eq47 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq40 eq19 -- backward demodulation 19,40
  have eq59 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq40 eq47 -- superposition 47,40, 40 into 47, unify on (0).2 in 40 and (0).2 in 47
  subsumption eq59 eq42


@[equational_result]
theorem Equation1927_implies_Equation1664 (G : Type*) [Magma G] (h : Equation1927 G) : Equation1664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq23 -- superposition 23,12, 12 into 23, unify on (0).2 in 12 and (0).1.2 in 23
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq14 eq23 -- superposition 23,14, 14 into 23, unify on (0).2 in 14 and (0).1.2 in 23
  have eq47 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq40 eq19 -- backward demodulation 19,40
  have eq59 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq40 eq47 -- superposition 47,40, 40 into 47, unify on (0).2 in 40 and (0).2 in 47
  subsumption eq59 eq42


@[equational_result]
theorem Equation1328_implies_Equation3292 (G : Type*) [Magma G] (h : Equation1328 G) : Equation3292 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq34 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq34 eq16


@[equational_result]
theorem Equation1328_implies_Equation1244 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1244 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1328_implies_Equation1150 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation1328_implies_Equation3255 (G : Type*) [Magma G] (h : Equation1328 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation1328_implies_Equation3322 (G : Type*) [Magma G] (h : Equation1328 G) : Equation3322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 rfl


@[equational_result]
theorem Equation1328_implies_Equation1137 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1137 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation1328_implies_Equation1724 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


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
theorem Equation1328_implies_Equation1051 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1051 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq13 eq11


@[equational_result]
theorem Equation1328_implies_Equation117 (G : Type*) [Magma G] (h : Equation1328 G) : Equation117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation1328_implies_Equation3274 (G : Type*) [Magma G] (h : Equation1328 G) : Equation3274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq34 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).2 in 13
  subsumption eq34 eq16


@[equational_result]
theorem Equation1328_implies_Equation1767 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1767 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation1328_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1291_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation2070 (G : Type*) [Magma G] (h : Equation1291 G) : Equation2070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation3431 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3431 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation1328 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1328 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation4128 (G : Type*) [Magma G] (h : Equation1291 G) : Equation4128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq44 (X0 : G) : (X0 ◇ sK1) ≠ (((X0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).1 in 10
  subsumption eq44 eq14


@[equational_result]
theorem Equation1291_implies_Equation1322 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1063 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation3284 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3284 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation4138 (G : Type*) [Magma G] (h : Equation1291 G) : Equation4138 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq44 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK2) ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1.1 in 10
  subsumption eq44 eq14


@[equational_result]
theorem Equation1291_implies_Equation124 (G : Type*) [Magma G] (h : Equation1291 G) : Equation124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation3349 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3349 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation1217 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK4 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation3271 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK0) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation3346 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3346 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation2186 (G : Type*) [Magma G] (h : Equation1291 G) : Equation2186 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1291_implies_Equation1738 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1738 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1291_implies_Equation3309 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3309 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 rfl


@[equational_result]
theorem Equation1291_implies_Equation1048 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation3343 (G : Type*) [Magma G] (h : Equation1291 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq33 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq15 eq13 -- superposition 13,15, 15 into 13, unify on (0).2 in 15 and (0).2 in 13
  subsumption eq33 eq15


@[equational_result]
theorem Equation1291_implies_Equation1041 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation1234 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1234 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1291_implies_Equation2043 (G : Type*) [Magma G] (h : Equation1291 G) : Equation2043 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1291_implies_Equation1318 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1904 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1291_implies_Equation1697 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1336 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1336 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq15 rfl


@[equational_result]
theorem Equation1291_implies_Equation1119 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1119 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation1175_implies_Equation1225 (G : Type*) [Magma G] (h : Equation1175 G) : Equation1225 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X5) = (X1 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 X5 : G) : (X1 ◇ X5) = (X4 ◇ X5) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq21 (X0 : G) : sK0 ≠ (sK0 ◇ (((X0 ◇ sK0) ◇ sK1) ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.1.1 in 10
  subsumption eq21 eq11


@[equational_result]
theorem Equation1175_implies_Equation516 (G : Type*) [Magma G] (h : Equation1175 G) : Equation516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X5) = (X1 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 X5 : G) : (X1 ◇ X5) = (X4 ◇ X5) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq24 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ X3)) = X3 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq39 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq39 eq24


@[equational_result]
theorem Equation1175_implies_Equation2074 (G : Type*) [Magma G] (h : Equation1175 G) : Equation2074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X5) = (X1 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 X5 : G) : (X1 ◇ X5) = (X4 ◇ X5) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq26 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ X3)) = X3 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq28 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (X0 ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq28 eq26


@[equational_result]
theorem Equation1175_implies_Equation130 (G : Type*) [Magma G] (h : Equation1175 G) : Equation130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X5)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X5) = (X1 ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X1 X4 X5 : G) : (X1 ◇ X5) = (X4 ◇ X5) := superpose eq11 eq13 -- forward demodulation 13,11
  have eq21 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK2) ◇ sK0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2.1 in 10
  subsumption eq21 eq11


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
theorem Equation1734_implies_Equation1834 (G : Type*) [Magma G] (h : Equation1734 G) : Equation1834 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq28 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X3 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.1 in 11
  have eq44 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X3 := superpose eq31 eq28 -- backward demodulation 28,31
  have eq46 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq44 eq11 -- backward demodulation 11,44
  have eq55 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq55 eq46


@[equational_result]
theorem Equation2195_implies_Equation1734 (G : Type*) [Magma G] (h : Equation2195 G) : Equation1734 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation2195_implies_Equation2148 (G : Type*) [Magma G] (h : Equation2195 G) : Equation2148 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq12


@[equational_result]
theorem Equation2195_implies_Equation1254 (G : Type*) [Magma G] (h : Equation2195 G) : Equation1254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq19 -- forward demodulation 19,14
  subsumption eq20 eq12


@[equational_result]
theorem Equation2195_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2195 G) : Equation2097 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation2195_implies_Equation1746 (G : Type*) [Magma G] (h : Equation2195 G) : Equation1746 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation2195_implies_Equation1871 (G : Type*) [Magma G] (h : Equation2195 G) : Equation1871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq19 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq12


@[equational_result]
theorem Equation1125_implies_Equation1262 (G : Type*) [Magma G] (h : Equation1125 G) : Equation1262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ X3) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq30 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ sK1) ◇ sK0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.2.1 in 10
  subsumption eq30 eq13


@[equational_result]
theorem Equation1125_implies_Equation483 (G : Type*) [Magma G] (h : Equation1125 G) : Equation483 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq21 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq21 eq13


@[equational_result]
theorem Equation1125_implies_Equation2195 (G : Type*) [Magma G] (h : Equation1125 G) : Equation2195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ X3) := superpose eq13 eq19 -- forward demodulation 19,13
  have eq30 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ sK0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq30 eq13


@[equational_result]
theorem Equation1125_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1125 G) : Equation1924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq21 eq13


@[equational_result]
theorem Equation1257_implies_Equation851 (G : Type*) [Magma G] (h : Equation1257 G) : Equation851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1257_implies_Equation847 (G : Type*) [Magma G] (h : Equation1257 G) : Equation847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1257_implies_Equation843 (G : Type*) [Magma G] (h : Equation1257 G) : Equation843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1257_implies_Equation848 (G : Type*) [Magma G] (h : Equation1257 G) : Equation848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation1257_implies_Equation844 (G : Type*) [Magma G] (h : Equation1257 G) : Equation844 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation851_implies_Equation1257 (G : Type*) [Magma G] (h : Equation851 G) : Equation1257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation100 (G : Type*) [Magma G] (h : Equation851 G) : Equation100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq25 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation851_implies_Equation1255 (G : Type*) [Magma G] (h : Equation851 G) : Equation1255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation1250 (G : Type*) [Magma G] (h : Equation851 G) : Equation1250 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation851_implies_Equation109 (G : Type*) [Magma G] (h : Equation851 G) : Equation109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation851_implies_Equation1227 (G : Type*) [Magma G] (h : Equation851 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq41 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq41 rfl


@[equational_result]
theorem Equation851_implies_Equation1226 (G : Type*) [Magma G] (h : Equation851 G) : Equation1226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq41 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq41 rfl


@[equational_result]
theorem Equation851_implies_Equation1254 (G : Type*) [Magma G] (h : Equation851 G) : Equation1254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X5) ◇ X0)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation1265_implies_Equation1068 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation849 (G : Type*) [Magma G] (h : Equation1265 G) : Equation849 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X0 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1265_implies_Equation1046 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1046 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation1052 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation1056 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation1060 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1265_implies_Equation1042 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1042 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X0)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation1068_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1265 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1243 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1263 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation111 (G : Type*) [Magma G] (h : Equation1068 G) : Equation111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation1068_implies_Equation1262 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1262 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation1068_implies_Equation1230 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1230 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq128 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq128 rfl


@[equational_result]
theorem Equation1068_implies_Equation1264 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq144 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq144 rfl


@[equational_result]
theorem Equation441_implies_Equation650 (G : Type*) [Magma G] (h : Equation441 G) : Equation650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation1882 (G : Type*) [Magma G] (h : Equation441 G) : Equation1882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK3 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3940 (G : Type*) [Magma G] (h : Equation441 G) : Equation3940 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation639 (G : Type*) [Magma G] (h : Equation441 G) : Equation639 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation655 (G : Type*) [Magma G] (h : Equation441 G) : Equation655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation1061 (G : Type*) [Magma G] (h : Equation441 G) : Equation1061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3873 (G : Type*) [Magma G] (h : Equation441 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation3931 (G : Type*) [Magma G] (h : Equation441 G) : Equation3931 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation3667 (G : Type*) [Magma G] (h : Equation441 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3939 (G : Type*) [Magma G] (h : Equation441 G) : Equation3939 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation3673 (G : Type*) [Magma G] (h : Equation441 G) : Equation3673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation633 (G : Type*) [Magma G] (h : Equation441 G) : Equation633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation4434 (G : Type*) [Magma G] (h : Equation441 G) : Equation4434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation455 (G : Type*) [Magma G] (h : Equation441 G) : Equation455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3919 (G : Type*) [Magma G] (h : Equation441 G) : Equation3919 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3747 (G : Type*) [Magma G] (h : Equation441 G) : Equation3747 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK3 ◇ sK4)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation4440 (G : Type*) [Magma G] (h : Equation441 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3875 (G : Type*) [Magma G] (h : Equation441 G) : Equation3875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation1050 (G : Type*) [Magma G] (h : Equation441 G) : Equation1050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation441_implies_Equation861 (G : Type*) [Magma G] (h : Equation441 G) : Equation861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation647 (G : Type*) [Magma G] (h : Equation441 G) : Equation647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation1271 (G : Type*) [Magma G] (h : Equation441 G) : Equation1271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK3) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK3)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation1043 (G : Type*) [Magma G] (h : Equation441 G) : Equation1043 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation1037 (G : Type*) [Magma G] (h : Equation441 G) : Equation1037 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq14


@[equational_result]
theorem Equation441_implies_Equation4 (G : Type*) [Magma G] (h : Equation441 G) : Equation4 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation2048 (G : Type*) [Magma G] (h : Equation441 G) : Equation2048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq19 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation441_implies_Equation2057 (G : Type*) [Magma G] (h : Equation441 G) : Equation2057 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq14 eq17 -- forward demodulation 17,14
  have eq19 : sK0 ≠ (sK0 ◇ sK2) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq14


@[equational_result]
theorem Equation441_implies_Equation454 (G : Type*) [Magma G] (h : Equation441 G) : Equation454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation361 (G : Type*) [Magma G] (h : Equation441 G) : Equation361 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation4507 (G : Type*) [Magma G] (h : Equation441 G) : Equation4507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3672 (G : Type*) [Magma G] (h : Equation441 G) : Equation3672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation649 (G : Type*) [Magma G] (h : Equation441 G) : Equation649 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3866 (G : Type*) [Magma G] (h : Equation441 G) : Equation3866 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3670 (G : Type*) [Magma G] (h : Equation441 G) : Equation3670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation363 (G : Type*) [Magma G] (h : Equation441 G) : Equation363 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3947 (G : Type*) [Magma G] (h : Equation441 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation441_implies_Equation3874 (G : Type*) [Magma G] (h : Equation441 G) : Equation3874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation450 (G : Type*) [Magma G] (h : Equation441 G) : Equation450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation643 (G : Type*) [Magma G] (h : Equation441 G) : Equation643 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation856 (G : Type*) [Magma G] (h : Equation441 G) : Equation856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3929 (G : Type*) [Magma G] (h : Equation441 G) : Equation3929 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation653 (G : Type*) [Magma G] (h : Equation441 G) : Equation653 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3930 (G : Type*) [Magma G] (h : Equation441 G) : Equation3930 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3933 (G : Type*) [Magma G] (h : Equation441 G) : Equation3933 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK3) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation4433 (G : Type*) [Magma G] (h : Equation441 G) : Equation4433 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation4517 (G : Type*) [Magma G] (h : Equation441 G) : Equation4517 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation632 (G : Type*) [Magma G] (h : Equation441 G) : Equation632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation441_implies_Equation3718 (G : Type*) [Magma G] (h : Equation441 G) : Equation3718 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation441_implies_Equation3744 (G : Type*) [Magma G] (h : Equation441 G) : Equation3744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq12 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK3 ◇ sK1)) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation650_implies_Equation448 (G : Type*) [Magma G] (h : Equation650 G) : Equation448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) = ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq372 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq12 -- superposition 12,55, 55 into 12, unify on (0).2 in 55 and (0).1.2.1.2 in 12
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1578 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1693 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1578 -- forward demodulation 1578,11
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1695 -- superposition 1695,31, 31 into 1695, unify on (0).2 in 31 and (0).2.2.2 in 1695
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1695 eq9 -- superposition 9,1695, 1695 into 9, unify on (0).2 in 1695 and (0).1.2.2 in 9
  have eq1883 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1695 eq12 -- superposition 12,1695, 1695 into 12, unify on (0).2 in 1695 and (0).1.2.1.2 in 12
  have eq2683 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1693 eq12 -- superposition 12,1693, 1693 into 12, unify on (0).2 in 1693 and (0).1.2.1.2 in 12
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1878 -- superposition 1878,31, 31 into 1878, unify on (0).2 in 31 and (0).2.2.1.2 in 1878
  have eq2760 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1883 -- superposition 1883,31, 31 into 1883, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1883
  have eq2846 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1436 -- superposition 1436,11, 11 into 1436, unify on (0).2 in 11 and (0).1.2.1.2 in 1436
  have eq2902 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1518 -- superposition 1518,21, 21 into 1518, unify on (0).2 in 21 and (0).1 in 1518
  have eq3015 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2902 eq2760 -- backward demodulation 2760,2902
  have eq3016 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2902 eq2688 -- backward demodulation 2688,2902
  have eq3017 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2902 eq1874 -- backward demodulation 1874,2902
  have eq3019 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3015 -- forward demodulation 3015,11
  have eq3020 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3027 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3017 eq2846 -- backward demodulation 2846,3017
  have eq3160 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3020 eq3019 -- superposition 3019,3020, 3020 into 3019, unify on (0).2 in 3020 and (0).1.2 in 3019
  have eq3180 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3020 eq372 -- superposition 372,3020, 3020 into 372, unify on (0).2 in 3020 and (0).1.2.1.1 in 372
  have eq3226 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3020 eq30 -- superposition 30,3020, 3020 into 30, unify on (0).2 in 3020 and (0).1.2.1 in 30
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3160 eq3027 -- backward demodulation 3027,3160
  have eq3252 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3017 eq3226 -- forward demodulation 3226,3017
  have eq3255 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3252 eq2683 -- backward demodulation 2683,3252
  have eq3300 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3250 eq55 -- superposition 55,3250, 3250 into 55, unify on (0).2 in 3250 and (0).2.2 in 55
  have eq3301 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3250 eq271 -- superposition 271,3250, 3250 into 271, unify on (0).2 in 3250 and (0).2.2.1 in 271
  have eq3310 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3300 eq3180 -- backward demodulation 3180,3300
  have eq3312 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3300 eq3301 -- forward demodulation 3301,3300
  have eq3326 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3312 eq3255 -- backward demodulation 3255,3312
  have eq3413 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq33 -- superposition 33,3312, 3312 into 33, unify on (0).2 in 3312 and (0).1.2.1 in 33
  have eq3457 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3312 eq9 -- superposition 9,3312, 3312 into 9, unify on (0).2 in 3312 and (0).1.2 in 9
  have eq3534 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3312 eq21 -- superposition 21,3312, 3312 into 21, unify on (0).2 in 3312 and (0).1 in 21
  have eq3592 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq3413 -- forward demodulation 3413,3312
  have eq3658 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3312 eq3457 -- superposition 3457,3312, 3312 into 3457, unify on (0).2 in 3312 and (0).1.2 in 3457
  have eq3687 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3457 eq3312 -- superposition 3312,3457, 3457 into 3312, unify on (0).2 in 3457 and (0).1 in 3312
  have eq3869 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3658 eq3310 -- backward demodulation 3310,3658
  have eq4077 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3869 eq11 -- superposition 11,3869, 3869 into 11, unify on (0).2 in 3869 and (0).1.2.1 in 11
  have eq4166 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3869 eq3687 -- superposition 3687,3869, 3869 into 3687, unify on (0).2 in 3869 and (0).1.2.2 in 3687
  have eq4202 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4166 eq4077 -- backward demodulation 4077,4166
  have eq4757 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4202 eq3534 -- backward demodulation 3534,4202
  have eq5316 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4202 eq3326 -- backward demodulation 3326,4202
  have eq5862 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5316 eq4757 -- backward demodulation 4757,5316
  have eq5895 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5862 eq3592 -- backward demodulation 3592,5862
  have eq5914 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3658 eq5895 -- forward demodulation 5895,3658
  have eq5922 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5914 eq3687 -- backward demodulation 3687,5914
  have eq5936 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5914 eq10 -- backward demodulation 10,5914
  subsumption eq5936 eq5922


@[equational_result]
theorem Equation650_implies_Equation4403 (G : Type*) [Magma G] (h : Equation650 G) : Equation4403 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1 in 12
  have eq14 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) ◇ (X3 ◇ X0)))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.2.1 in 12
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) = ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2.2 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq34 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq81 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))))) := superpose eq21 eq38 -- superposition 38,21, 21 into 38, unify on (0).2 in 21 and (0).1.2.1.2 in 38
  have eq105 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)))) := superpose eq9 eq81 -- forward demodulation 81,9
  have eq231 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X5 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2))) = X2 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1.2.1 in 12
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).2.2.1.2 in 34
  have eq390 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq12 -- superposition 12,55, 55 into 12, unify on (0).2 in 55 and (0).1.2.1.2 in 12
  have eq743 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq11 eq231 -- superposition 231,11, 11 into 231, unify on (0).2 in 11 and (0).1.2.1.2 in 231
  have eq1097 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3)) = ((X3 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) ◇ (((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))))) := superpose eq34 eq31 -- superposition 31,34, 34 into 31, unify on (0).2 in 34 and (0).1.2.1 in 31
  have eq1135 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X5))) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1.2.1 in 11
  have eq1140 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ ((X4 ◇ ((X3 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4)) ◇ ((X5 ◇ ((X6 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq31 eq14 -- superposition 14,31, 31 into 14, unify on (0).2 in 31 and (0).1 in 14
  have eq1173 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))) := superpose eq9 eq1097 -- forward demodulation 1097,9
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq38 -- superposition 38,23, 23 into 38, unify on (0).2 in 23 and (0).1.2.1 in 38
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1544 (X0 X1 X2 X4 : G) : (X4 ◇ (((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq23 eq390 -- superposition 390,23, 23 into 390, unify on (0).2 in 23 and (0).1.2.1.1 in 390
  have eq1551 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq1435 eq1544 -- forward demodulation 1544,1435
  have eq1579 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq35 -- superposition 35,13, 13 into 35, unify on (0).2 in 13 and (0).2.2.1.2.1 in 35
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq34 eq35 -- superposition 35,34, 34 into 35, unify on (0).2 in 34 and (0).2.2.1.2.1 in 35
  have eq1694 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1699 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq11 eq1551 -- superposition 1551,11, 11 into 1551, unify on (0).2 in 11 and (0).1.2.1.2 in 1551
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1880 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1885 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2287 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) = ((X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq24 eq30 -- superposition 30,24, 24 into 30, unify on (0).2 in 24 and (0).1.2.1 in 30
  have eq2684 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq1694 eq21 -- superposition 21,1694, 1694 into 21, unify on (0).2 in 1694 and (0).2.2.2 in 21
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1880 -- superposition 1880,31, 31 into 1880, unify on (0).2 in 31 and (0).2.2.1.2 in 1880
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1885 -- superposition 1885,31, 31 into 1885, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1885
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3024 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq3018 eq1699 -- backward demodulation 1699,3018
  have eq3028 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3184 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3021 eq30 -- superposition 30,3021, 3021 into 30, unify on (0).2 in 3021 and (0).1.2.1 in 30
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3028 -- backward demodulation 3028,3161
  have eq3252 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3018 eq3184 -- forward demodulation 3184,3018
  have eq3258 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := superpose eq3252 eq2684 -- backward demodulation 2684,3252
  have eq3303 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3304 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3316 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3303 eq3304 -- forward demodulation 3304,3303
  have eq3331 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq3316 eq3258 -- backward demodulation 3258,3316
  have eq3435 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq3331 eq390 -- backward demodulation 390,3331
  have eq3450 (X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq3331 eq743 -- backward demodulation 743,3331
  have eq3547 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq3331 eq2287 -- backward demodulation 2287,3331
  have eq3695 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) = X0 := superpose eq3303 eq3435 -- forward demodulation 3435,3303
  have eq3837 (X0 X1 X2 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ (X6 ◇ (X2 ◇ X6))) := superpose eq3331 eq3547 -- forward demodulation 3547,3331
  have eq3860 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4))) := superpose eq3837 eq34 -- backward demodulation 34,3837
  have eq4294 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ (X2 ◇ X3))) = X3 := superpose eq1519 eq3695 -- superposition 3695,1519, 1519 into 3695, unify on (0).2 in 1519 and (0).1.2.1 in 3695
  have eq4636 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq3860 eq3860 -- superposition 3860,3860, 3860 into 3860, unify on (0).2 in 3860 and (0).2.2.2 in 3860
  have eq4741 (X0 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ (X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3))) := superpose eq3837 eq4636 -- forward demodulation 4636,3837
  have eq4746 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2))) := superpose eq4741 eq105 -- backward demodulation 105,4741
  have eq4759 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq4746 eq1173 -- backward demodulation 1173,4746
  have eq4762 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq4759 eq3450 -- backward demodulation 3450,4759
  have eq4852 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X2 := superpose eq1519 eq4762 -- superposition 4762,1519, 1519 into 4762, unify on (0).2 in 1519 and (0).1.2 in 4762
  have eq4880 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) ◇ X5) := superpose eq4852 eq1135 -- backward demodulation 1135,4852
  have eq4881 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ ((X6 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4852 eq1140 -- backward demodulation 1140,4852
  have eq4886 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ X0) := superpose eq4852 eq1519 -- backward demodulation 1519,4852
  have eq4918 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X3 := superpose eq4886 eq4294 -- backward demodulation 4294,4886
  have eq4949 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq4918 eq3024 -- backward demodulation 3024,4918
  have eq5240 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4949 eq4881 -- backward demodulation 4881,4949
  have eq6019 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ (X5 ◇ (X6 ◇ X5)))) := superpose eq4949 eq5240 -- forward demodulation 5240,4949
  have eq6020 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4) := superpose eq4949 eq6019 -- forward demodulation 6019,4949
  have eq6025 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) = ((X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5) := superpose eq6020 eq4880 -- backward demodulation 4880,6020
  have eq6042 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq4949 eq6025 -- forward demodulation 6025,4949
  have eq6514 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq6042 eq10 -- backward demodulation 10,6042
  have eq6515 : sK0 ≠ (sK0 ◇ sK2) := superpose eq6042 eq6514 -- forward demodulation 6514,6042
  subsumption eq6515 eq6042


