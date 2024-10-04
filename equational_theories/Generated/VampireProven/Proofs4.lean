import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1842_implies_Equation1641 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1641 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) := mod_symm nh
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
  have eq116 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq108 eq10 -- backward demodulation 10,108
  subsumption eq116 eq113


@[equational_result]
theorem Equation1842_implies_Equation3054 (G : Type*) [Magma G] (h : Equation1842 G) : Equation3054 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq90 eq15 -- backward demodulation 15,90
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq93 eq9 -- backward demodulation 9,93
  have eq107 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq93 eq90 -- backward demodulation 90,93
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq107 eq109 -- backward demodulation 109,107
  have eq115 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq107 eq10 -- backward demodulation 10,107
  subsumption eq115 eq112


@[equational_result]
theorem Equation1842_implies_Equation1664 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
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
  have eq117 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq113 eq10 -- backward demodulation 10,113
  subsumption eq117 eq113


@[equational_result]
theorem Equation1842_implies_Equation4075 (G : Type*) [Magma G] (h : Equation1842 G) : Equation4075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq90 eq15 -- backward demodulation 15,90
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq93 eq9 -- backward demodulation 9,93
  have eq107 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq93 eq90 -- backward demodulation 90,93
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq110 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK2) := superpose eq109 eq10 -- backward demodulation 10,109
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq107 eq109 -- backward demodulation 109,107
  have eq116 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq107 eq110 -- backward demodulation 110,107
  have eq139 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq101 eq113 -- superposition 113,101, 101 into 113, unify on (0).2 in 101 and (0).1.1 in 113
  have eq175 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq139 eq116 -- superposition 116,139, 139 into 116, unify on (0).2 in 139 and (0).2 in 116
  subsumption eq175 eq139


@[equational_result]
theorem Equation1842_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1645 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq63 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq83 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq67 eq37 -- backward demodulation 37,67
  have eq86 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq83 -- forward demodulation 83,15
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq86 eq30 -- backward demodulation 30,86
  have eq92 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq88 -- forward demodulation 88,9
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq92 eq15 -- backward demodulation 15,92
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq95 eq92 -- backward demodulation 92,95
  have eq132 : sK0 ≠ sK0 := superpose eq109 eq63 -- superposition 63,109, 109 into 63, unify on (0).2 in 109 and (0).2 in 63
  subsumption eq132 rfl


@[equational_result]
theorem Equation1842_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1648 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq63 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq82 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq65 eq37 -- backward demodulation 37,65
  have eq85 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq82 -- forward demodulation 82,15
  have eq87 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq85 eq30 -- backward demodulation 30,85
  have eq91 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq87 -- forward demodulation 87,9
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq91 eq15 -- backward demodulation 15,91
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq131 : sK0 ≠ sK0 := superpose eq108 eq63 -- superposition 63,108, 108 into 63, unify on (0).2 in 108 and (0).2 in 63
  subsumption eq131 rfl


@[equational_result]
theorem Equation1842_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK3) ◇ sK0)) := mod_symm nh
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
  have eq117 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq113 eq10 -- backward demodulation 10,113
  subsumption eq117 eq113


@[equational_result]
theorem Equation1842_implies_Equation2450 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq91 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq90 eq11 -- backward demodulation 11,90
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq90 eq15 -- backward demodulation 15,90
  have eq101 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq91 eq10 -- backward demodulation 10,91
  have eq102 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq93 eq9 -- backward demodulation 9,93
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq93 eq90 -- backward demodulation 90,93
  have eq110 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq93 eq101 -- backward demodulation 101,93
  have eq111 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq102 eq64 -- backward demodulation 64,102
  have eq114 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq108 eq111 -- backward demodulation 111,108
  subsumption eq110 eq114


@[equational_result]
theorem Equation1842_implies_Equation1877 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) := mod_symm nh
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
theorem Equation1842_implies_Equation1845 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1845 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := mod_symm nh
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
  have eq110 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := superpose eq94 eq10 -- backward demodulation 10,94
  have eq111 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq102 eq66 -- backward demodulation 66,102
  have eq114 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq108 eq111 -- backward demodulation 111,108
  subsumption eq110 eq114


@[equational_result]
theorem Equation1842_implies_Equation1854 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1854 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK1)) := mod_symm nh
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
theorem Equation1842_implies_Equation2444 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
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
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq91 eq11 -- backward demodulation 11,91
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq91 eq15 -- backward demodulation 15,91
  have eq102 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq92 eq10 -- backward demodulation 10,92
  have eq103 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq94 eq9 -- backward demodulation 9,94
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq111 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq94 eq102 -- backward demodulation 102,94
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq103 eq66 -- backward demodulation 66,103
  have eq115 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq109 eq112 -- backward demodulation 112,109
  subsumption eq111 eq115


@[equational_result]
theorem Equation1842_implies_Equation2453 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2453 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ sK1) := mod_symm nh
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
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq91 eq11 -- backward demodulation 11,91
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq91 eq15 -- backward demodulation 15,91
  have eq102 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := superpose eq92 eq10 -- backward demodulation 10,92
  have eq103 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq94 eq9 -- backward demodulation 9,94
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq111 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq94 eq102 -- backward demodulation 102,94
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq103 eq66 -- backward demodulation 66,103
  have eq115 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq109 eq112 -- backward demodulation 112,109
  subsumption eq111 eq115


@[equational_result]
theorem Equation1842_implies_Equation2274 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) := mod_symm nh
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
theorem Equation1842_implies_Equation1652 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1652 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq63 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq83 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq67 eq37 -- backward demodulation 37,67
  have eq86 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq83 -- forward demodulation 83,15
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq86 eq30 -- backward demodulation 30,86
  have eq92 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq88 -- forward demodulation 88,9
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq92 eq15 -- backward demodulation 15,92
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq95 eq92 -- backward demodulation 92,95
  have eq132 : sK0 ≠ sK0 := superpose eq109 eq63 -- superposition 63,109, 109 into 63, unify on (0).2 in 109 and (0).2 in 63
  subsumption eq132 rfl


@[equational_result]
theorem Equation1842_implies_Equation4130 (G : Type*) [Magma G] (h : Equation1842 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq90 eq15 -- backward demodulation 15,90
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq93 eq9 -- backward demodulation 9,93
  have eq107 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq93 eq90 -- backward demodulation 90,93
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq110 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq109 eq10 -- backward demodulation 10,109
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq107 eq109 -- backward demodulation 109,107
  have eq116 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq107 eq110 -- backward demodulation 110,107
  have eq139 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq101 eq113 -- superposition 113,101, 101 into 113, unify on (0).2 in 101 and (0).1.1 in 113
  have eq175 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ X0) := superpose eq139 eq116 -- superposition 116,139, 139 into 116, unify on (0).2 in 139 and (0).1 in 116
  subsumption eq175 eq139


@[equational_result]
theorem Equation1842_implies_Equation1467 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK2))) := mod_symm nh
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
theorem Equation1842_implies_Equation2288 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := mod_symm nh
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
theorem Equation1842_implies_Equation1673 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK1)) := mod_symm nh
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
  have eq117 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq113 eq10 -- backward demodulation 10,113
  subsumption eq117 eq113


@[equational_result]
theorem Equation1842_implies_Equation1651 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq63 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq47 eq10 -- superposition 10,47, 47 into 10, unify on (0).2 in 47 and (0).2 in 10
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq83 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq67 eq37 -- backward demodulation 37,67
  have eq86 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq83 -- forward demodulation 83,15
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq86 eq30 -- backward demodulation 30,86
  have eq92 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq88 -- forward demodulation 88,9
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq92 eq15 -- backward demodulation 15,92
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq95 eq92 -- backward demodulation 92,95
  have eq132 : sK0 ≠ sK0 := superpose eq109 eq63 -- superposition 63,109, 109 into 63, unify on (0).2 in 109 and (0).2 in 63
  subsumption eq132 rfl


@[equational_result]
theorem Equation1842_implies_Equation2281 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := mod_symm nh
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
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq124 : sK0 ≠ sK0 := superpose eq108 eq10 -- superposition 10,108, 108 into 10, unify on (0).2 in 108 and (0).2 in 10
  subsumption eq124 rfl


@[equational_result]
theorem Equation1842_implies_Equation1636 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.2 in 12
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.2 in 12
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.2 in 15
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2.1 in 15
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq38 eq22 -- backward demodulation 22,38
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq47 eq15 -- superposition 15,47, 47 into 15, unify on (0).2 in 47 and (0).1 in 15
  have eq81 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq64 eq37 -- backward demodulation 37,64
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq81 -- forward demodulation 81,15
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq84 eq30 -- backward demodulation 30,84
  have eq90 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq86 -- forward demodulation 86,9
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq90 eq15 -- backward demodulation 15,90
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq93 eq9 -- backward demodulation 9,93
  have eq107 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq93 eq90 -- backward demodulation 90,93
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq101 eq64 -- backward demodulation 64,101
  have eq110 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := superpose eq109 eq10 -- backward demodulation 10,109
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq107 eq109 -- backward demodulation 109,107
  have eq116 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq107 eq110 -- backward demodulation 110,107
  subsumption eq116 eq113


@[equational_result]
theorem Equation1842_implies_Equation4143 (G : Type*) [Magma G] (h : Equation1842 G) : Equation4143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
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
  have eq111 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK0) ◇ sK2) := superpose eq110 eq10 -- backward demodulation 10,110
  have eq114 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq108 eq110 -- backward demodulation 110,108
  have eq117 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq108 eq111 -- backward demodulation 111,108
  have eq140 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq102 eq114 -- superposition 114,102, 102 into 114, unify on (0).2 in 102 and (0).1.1 in 114
  have eq176 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq140 eq117 -- superposition 117,140, 140 into 117, unify on (0).2 in 140 and (0).2 in 117
  subsumption eq176 eq140


@[equational_result]
theorem Equation1842_implies_Equation2254 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
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
theorem Equation1842_implies_Equation1465 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
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
theorem Equation1842_implies_Equation4136 (G : Type*) [Magma G] (h : Equation1842 G) : Equation4136 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
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
  have eq111 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK3) := superpose eq110 eq10 -- backward demodulation 10,110
  have eq114 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq108 eq110 -- backward demodulation 110,108
  have eq117 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK3) := superpose eq108 eq111 -- backward demodulation 111,108
  have eq140 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq102 eq114 -- superposition 114,102, 102 into 114, unify on (0).2 in 102 and (0).1.1 in 114
  have eq176 (X0 : G) : (sK0 ◇ sK1) ≠ (sK0 ◇ X0) := superpose eq140 eq117 -- superposition 117,140, 140 into 117, unify on (0).2 in 140 and (0).2 in 117
  subsumption eq176 eq140


@[equational_result]
theorem Equation1842_implies_Equation2273 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := mod_symm nh
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
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq91 -- backward demodulation 91,94
  have eq124 : sK0 ≠ sK0 := superpose eq108 eq10 -- superposition 10,108, 108 into 10, unify on (0).2 in 108 and (0).2 in 10
  subsumption eq124 rfl


@[equational_result]
theorem Equation1842_implies_Equation1432 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1432 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
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
theorem Equation1842_implies_Equation2260 (G : Type*) [Magma G] (h : Equation1842 G) : Equation2260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := mod_symm nh
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
theorem Equation1842_implies_Equation1869 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := mod_symm nh
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
theorem Equation424_implies_Equation423 (G : Type*) [Magma G] (h : Equation424 G) : Equation423 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation424_implies_Equation617 (G : Type*) [Magma G] (h : Equation424 G) : Equation617 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation424_implies_Equation3318 (G : Type*) [Magma G] (h : Equation424 G) : Equation3318 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2.2 in 13
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 rfl


@[equational_result]
theorem Equation424_implies_Equation3253 (G : Type*) [Magma G] (h : Equation424 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation424_implies_Equation821 (G : Type*) [Magma G] (h : Equation424 G) : Equation821 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq13


@[equational_result]
theorem Equation424_implies_Equation1837 (G : Type*) [Magma G] (h : Equation424 G) : Equation1837 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.2.2 in 13
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq15 eq14 -- backward demodulation 14,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation424_implies_Equation1832 (G : Type*) [Magma G] (h : Equation424 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq11 eq9 -- backward demodulation 9,11
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq13 -- forward demodulation 13,11
  subsumption eq14 eq11


@[equational_result]
theorem Equation423_implies_Equation424 (G : Type*) [Magma G] (h : Equation423 G) : Equation424 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq59 : sK0 ≠ sK0 := superpose eq19 eq18 -- superposition 18,19, 19 into 18, unify on (0).2 in 19 and (0).2 in 18
  subsumption eq59 rfl


@[equational_result]
theorem Equation423_implies_Equation1223 (G : Type*) [Magma G] (h : Equation423 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1 in 12
  have eq17 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq18 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq17 -- forward demodulation 17,13
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq18 -- forward demodulation 18,13
  subsumption eq19 eq13


@[equational_result]
theorem Equation423_implies_Equation3320 (G : Type*) [Magma G] (h : Equation423 G) : Equation3320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq40 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1.2.2 in 18
  have eq58 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq40 eq10 -- backward demodulation 10,40
  subsumption eq58 rfl


@[equational_result]
theorem Equation423_implies_Equation419 (G : Type*) [Magma G] (h : Equation423 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq58 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq58 rfl


@[equational_result]
theorem Equation423_implies_Equation1022 (G : Type*) [Magma G] (h : Equation423 G) : Equation1022 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq40 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1.2.2 in 18
  have eq58 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq40 eq10 -- backward demodulation 10,40
  subsumption eq58 eq40


@[equational_result]
theorem Equation423_implies_Equation1838 (G : Type*) [Magma G] (h : Equation423 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq40 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1.2.2 in 18
  have eq58 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq40 eq10 -- backward demodulation 10,40
  subsumption eq58 eq40


@[equational_result]
theorem Equation423_implies_Equation421 (G : Type*) [Magma G] (h : Equation423 G) : Equation421 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1 in 13
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2.2 in 9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq14 eq17 -- forward demodulation 17,14
  have eq58 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq58 rfl


@[equational_result]
theorem Equation1260_implies_Equation839 (G : Type*) [Magma G] (h : Equation1260 G) : Equation839 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.2 in 9
  have eq140 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq55 eq15 -- superposition 15,55, 55 into 15, unify on (0).2 in 55 and (0).1.2.2 in 15
  have eq603 : sK0 ≠ sK0 := superpose eq140 eq10 -- superposition 10,140, 140 into 10, unify on (0).2 in 140 and (0).2 in 10
  subsumption eq603 rfl


@[equational_result]
theorem Equation1260_implies_Equation817 (G : Type*) [Magma G] (h : Equation1260 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1.1 in 8
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.1 in 10
  have eq14 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.2.2.1.1 in 10
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq8 eq12 -- forward demodulation 12,8
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq20 eq8 -- superposition 8,20, 20 into 8, unify on (0).2 in 20 and (0).1.2 in 8
  have eq130 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq54 eq14 -- superposition 14,54, 54 into 14, unify on (0).2 in 54 and (0).1.2.2 in 14
  have eq579 : sK0 ≠ sK0 := superpose eq130 eq9 -- superposition 9,130, 130 into 9, unify on (0).2 in 130 and (0).2 in 9
  subsumption eq579 rfl


@[equational_result]
theorem Equation1260_implies_Equation836 (G : Type*) [Magma G] (h : Equation1260 G) : Equation836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.2 in 9
  have eq140 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq55 eq15 -- superposition 15,55, 55 into 15, unify on (0).2 in 55 and (0).1.2.2 in 15
  have eq603 : sK0 ≠ sK0 := superpose eq140 eq10 -- superposition 10,140, 140 into 10, unify on (0).2 in 140 and (0).2 in 10
  subsumption eq603 rfl


@[equational_result]
theorem Equation1260_implies_Equation833 (G : Type*) [Magma G] (h : Equation1260 G) : Equation833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.2 in 9
  have eq140 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq55 eq15 -- superposition 15,55, 55 into 15, unify on (0).2 in 55 and (0).1.2.2 in 15
  have eq603 : sK0 ≠ sK0 := superpose eq140 eq10 -- superposition 10,140, 140 into 10, unify on (0).2 in 140 and (0).2 in 10
  subsumption eq603 rfl


@[equational_result]
theorem Equation1260_implies_Equation819 (G : Type*) [Magma G] (h : Equation1260 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1.1 in 11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).1.2 in 9
  have eq131 (X0 X1 X3 : G) : (X3 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq52 eq15 -- superposition 15,52, 52 into 15, unify on (0).2 in 52 and (0).1.2.2 in 15
  have eq580 : sK0 ≠ sK0 := superpose eq131 eq10 -- superposition 10,131, 131 into 10, unify on (0).2 in 131 and (0).2 in 10
  subsumption eq580 rfl


@[equational_result]
theorem Equation839_implies_Equation1260 (G : Type*) [Magma G] (h : Equation839 G) : Equation1260 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq140 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq140 rfl


@[equational_result]
theorem Equation839_implies_Equation1223 (G : Type*) [Magma G] (h : Equation839 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation839_implies_Equation1832 (G : Type*) [Magma G] (h : Equation839 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq20 eq13


@[equational_result]
theorem Equation839_implies_Equation3862 (G : Type*) [Magma G] (h : Equation839 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq20 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation99 (G : Type*) [Magma G] (h : Equation839 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 : sK0 ≠ sK0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2 in 9
  subsumption eq17 rfl


@[equational_result]
theorem Equation839_implies_Equation1055 (G : Type*) [Magma G] (h : Equation839 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation359 (G : Type*) [Magma G] (h : Equation839 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq106 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq47 eq9 -- superposition 9,47, 47 into 9, unify on (0).2 in 47 and (0).2 in 9
  subsumption eq106 rfl


@[equational_result]
theorem Equation839_implies_Equation1041 (G : Type*) [Magma G] (h : Equation839 G) : Equation1041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation4065 (G : Type*) [Magma G] (h : Equation839 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq13 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).1.2.1 in 12
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq55 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq47 eq9 -- backward demodulation 9,47
  subsumption eq55 eq47


@[equational_result]
theorem Equation839_implies_Equation3867 (G : Type*) [Magma G] (h : Equation839 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation839_implies_Equation1031 (G : Type*) [Magma G] (h : Equation839 G) : Equation1031 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation1028 (G : Type*) [Magma G] (h : Equation839 G) : Equation1028 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation3316 (G : Type*) [Magma G] (h : Equation839 G) : Equation3316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation839_implies_Equation1248 (G : Type*) [Magma G] (h : Equation839 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation1229 (G : Type*) [Magma G] (h : Equation839 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq126 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq126 rfl


@[equational_result]
theorem Equation839_implies_Equation1067 (G : Type*) [Magma G] (h : Equation839 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation4131 (G : Type*) [Magma G] (h : Equation839 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.2 in 14
  have eq56 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq48 eq10 -- backward demodulation 10,48
  subsumption eq56 eq48


@[equational_result]
theorem Equation839_implies_Equation1850 (G : Type*) [Magma G] (h : Equation839 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation839_implies_Equation3319 (G : Type*) [Magma G] (h : Equation839 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation839_implies_Equation1847 (G : Type*) [Magma G] (h : Equation839 G) : Equation1847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 eq14


@[equational_result]
theorem Equation839_implies_Equation3255 (G : Type*) [Magma G] (h : Equation839 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq21 rfl


@[equational_result]
theorem Equation839_implies_Equation1254 (G : Type*) [Magma G] (h : Equation839 G) : Equation1254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation107 (G : Type*) [Magma G] (h : Equation839 G) : Equation107 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation839_implies_Equation1249 (G : Type*) [Magma G] (h : Equation839 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ X4) ◇ X1)) = X4 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1.1 in 12
  have eq140 : sK0 ≠ sK0 := superpose eq29 eq10 -- superposition 10,29, 29 into 10, unify on (0).2 in 29 and (0).2 in 10
  subsumption eq140 rfl


@[equational_result]
theorem Equation106_implies_Equation1246 (G : Type*) [Magma G] (h : Equation106 G) : Equation1246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq17 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq9


@[equational_result]
theorem Equation106_implies_Equation3724 (G : Type*) [Magma G] (h : Equation106 G) : Equation3724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq49 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq49 rfl


@[equational_result]
theorem Equation106_implies_Equation3661 (G : Type*) [Magma G] (h : Equation106 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq54 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq15 eq12 -- superposition 12,15, 15 into 12, unify on (0).2 in 15 and (0).1.2 in 12
  have eq125 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq54 eq10 -- superposition 10,54, 54 into 10, unify on (0).2 in 54 and (0).2 in 10
  subsumption eq125 rfl


@[equational_result]
theorem Equation106_implies_Equation1243 (G : Type*) [Magma G] (h : Equation106 G) : Equation1243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.1 in 9
  have eq39 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1 in 15
  have eq83 : sK0 ≠ sK0 := superpose eq39 eq10 -- superposition 10,39, 39 into 10, unify on (0).2 in 39 and (0).2 in 10
  subsumption eq83 rfl


@[equational_result]
theorem Equation1246_implies_Equation106 (G : Type*) [Magma G] (h : Equation1246 G) : Equation106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq28 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation1246_implies_Equation105 (G : Type*) [Magma G] (h : Equation1246 G) : Equation105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq28 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq28 rfl


@[equational_result]
theorem Equation1246_implies_Equation1224 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1224 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq21 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq21 eq20


@[equational_result]
theorem Equation1246_implies_Equation3725 (G : Type*) [Magma G] (h : Equation1246 G) : Equation3725 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq60 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq22 eq10 -- superposition 10,22, 22 into 10, unify on (0).2 in 22 and (0).2 in 10
  subsumption eq60 rfl


@[equational_result]
theorem Equation1246_implies_Equation3659 (G : Type*) [Magma G] (h : Equation1246 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq8 eq11 -- forward demodulation 11,8
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.2.1.1 in 8
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq14 eq16 -- forward demodulation 16,14
  have eq59 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2 in 9
  subsumption eq59 rfl


@[equational_result]
theorem Equation1246_implies_Equation1247 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1247 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq120 : sK0 ≠ sK0 := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation1246_implies_Equation1245 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1245 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq15 eq16 -- forward demodulation 16,15
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq120 : sK0 ≠ sK0 := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq120 rfl


@[equational_result]
theorem Equation1246_implies_Equation1227 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1227 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.1.1 in 9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9 -- backward demodulation 9,15
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq15 eq17 -- forward demodulation 17,15
  have eq51 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq20 eq22 -- superposition 22,20, 20 into 22, unify on (0).2 in 20 and (0).1 in 22
  have eq109 : sK0 ≠ sK0 := superpose eq51 eq10 -- superposition 10,51, 51 into 10, unify on (0).2 in 51 and (0).2 in 10
  subsumption eq109 rfl


@[equational_result]
theorem Equation631_implies_Equation4469 (G : Type*) [Magma G] (h : Equation631 G) : Equation4469 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation631_implies_Equation3930 (G : Type*) [Magma G] (h : Equation631 G) : Equation3930 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation631_implies_Equation1052 (G : Type*) [Magma G] (h : Equation631 G) : Equation1052 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation631_implies_Equation4397 (G : Type*) [Magma G] (h : Equation631 G) : Equation4397 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK2) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK2) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation631_implies_Equation654 (G : Type*) [Magma G] (h : Equation631 G) : Equation654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation855_implies_Equation2851 (G : Type*) [Magma G] (h : Equation855 G) : Equation2851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ (sK0 ◇ sK2) := superpose eq15 eq16 -- forward demodulation 16,15
  subsumption eq20 eq15


@[equational_result]
theorem Equation855_implies_Equation651 (G : Type*) [Magma G] (h : Equation855 G) : Equation651 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation855_implies_Equation631 (G : Type*) [Magma G] (h : Equation855 G) : Equation631 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation855_implies_Equation53 (G : Type*) [Magma G] (h : Equation855 G) : Equation53 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation855_implies_Equation442 (G : Type*) [Magma G] (h : Equation855 G) : Equation442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq16 eq15


@[equational_result]
theorem Equation855_implies_Equation864 (G : Type*) [Magma G] (h : Equation855 G) : Equation864 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq16 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  subsumption eq15 eq16


@[equational_result]
theorem Equation855_implies_Equation4403 (G : Type*) [Magma G] (h : Equation855 G) : Equation4403 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq16 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq20 : sK0 ≠ (sK0 ◇ sK2) := superpose eq15 eq16 -- forward demodulation 16,15
  subsumption eq20 eq15


@[equational_result]
theorem Equation855_implies_Equation1244 (G : Type*) [Magma G] (h : Equation855 G) : Equation1244 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq9 -- backward demodulation 9,13
  have eq15 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq14 eq11 -- backward demodulation 11,14
  have eq19 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq15


@[equational_result]
theorem Equation438_implies_Equation3665 (G : Type*) [Magma G] (h : Equation438 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq15 -- forward demodulation 15,14
  subsumption eq18 eq13


@[equational_result]
theorem Equation438_implies_Equation3666 (G : Type*) [Magma G] (h : Equation438 G) : Equation3666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq14 eq15 -- forward demodulation 15,14
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq18 -- forward demodulation 18,14
  subsumption eq19 eq13


@[equational_result]
theorem Equation438_implies_Equation462 (G : Type*) [Magma G] (h : Equation438 G) : Equation462 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation438_implies_Equation662 (G : Type*) [Magma G] (h : Equation438 G) : Equation662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation438_implies_Equation3721 (G : Type*) [Magma G] (h : Equation438 G) : Equation3721 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq14


@[equational_result]
theorem Equation438_implies_Equation3928 (G : Type*) [Magma G] (h : Equation438 G) : Equation3928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 rfl


@[equational_result]
theorem Equation438_implies_Equation439 (G : Type*) [Magma G] (h : Equation438 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation438_implies_Equation3947 (G : Type*) [Magma G] (h : Equation438 G) : Equation3947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 rfl


@[equational_result]
theorem Equation438_implies_Equation4440 (G : Type*) [Magma G] (h : Equation438 G) : Equation4440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq14 eq17 -- forward demodulation 17,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation438_implies_Equation1035 (G : Type*) [Magma G] (h : Equation438 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq18 : sK0 ≠ (sK0 ◇ sK1) := superpose eq15 eq14 -- backward demodulation 14,15
  subsumption eq18 eq15


@[equational_result]
theorem Equation438_implies_Equation855 (G : Type*) [Magma G] (h : Equation438 G) : Equation855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK3))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq17 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq14


@[equational_result]
theorem Equation654_implies_Equation440 (G : Type*) [Magma G] (h : Equation654 G) : Equation440 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq28 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq36 : sK0 ≠ sK0 := superpose eq29 eq30 -- superposition 30,29, 29 into 30, unify on (0).2 in 29 and (0).2 in 30
  subsumption eq36 rfl


@[equational_result]
theorem Equation654_implies_Equation2084 (G : Type*) [Magma G] (h : Equation654 G) : Equation2084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq35 : sK0 ≠ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK2)) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq36 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK3) := superpose eq29 eq35 -- forward demodulation 35,29
  have eq37 : sK0 ≠ (sK0 ◇ sK3) := superpose eq29 eq36 -- forward demodulation 36,29
  subsumption eq37 eq29


@[equational_result]
theorem Equation654_implies_Equation438 (G : Type*) [Magma G] (h : Equation654 G) : Equation438 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq28 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X3 := superpose eq21 eq13 -- backward demodulation 13,21
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq9 -- backward demodulation 9,21
  have eq30 : sK0 ≠ (sK0 ◇ sK1) := superpose eq28 eq10 -- backward demodulation 10,28
  have eq36 : sK0 ≠ sK0 := superpose eq29 eq30 -- superposition 30,29, 29 into 30, unify on (0).2 in 29 and (0).2 in 30
  subsumption eq36 rfl


@[equational_result]
theorem Equation654_implies_Equation363 (G : Type*) [Magma G] (h : Equation654 G) : Equation363 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq9 eq11 -- forward demodulation 11,9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq9 -- backward demodulation 9,22
  have eq35 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq29 eq10 -- backward demodulation 10,29
  have eq36 : sK0 ≠ (sK0 ◇ sK2) := superpose eq29 eq35 -- forward demodulation 35,29
  subsumption eq36 eq29


@[equational_result]
theorem Equation3892_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3892_implies_Equation4591 (G : Type*) [Magma G] (h : Equation3892 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq61 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq61 eq15


@[equational_result]
theorem Equation3892_implies_Equation4090 (G : Type*) [Magma G] (h : Equation3892 G) : Equation4090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq56 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq56 eq15


@[equational_result]
theorem Equation3892_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq26 eq15


@[equational_result]
theorem Equation3892_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3892_implies_Equation3905 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3905 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3892_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK3) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3892_implies_Equation4093 (G : Type*) [Magma G] (h : Equation3892 G) : Equation4093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq61 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq61 eq15


@[equational_result]
theorem Equation3892_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3892_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).1 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3892_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3892_implies_Equation3871 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq16 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ (X0 ◇ X0)) ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3907_implies_Equation3892 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3892 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.2 in 10
  have eq48 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = ((X4 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.2 in 9
  have eq57 (X1 X2 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ sK2) := superpose eq14 eq22 -- superposition 22,14, 14 into 22, unify on (0).2 in 14 and (0).2.1.2 in 22
  subsumption eq57 eq48


@[equational_result]
theorem Equation3907_implies_Equation4066 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq57 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq57 eq14


@[equational_result]
theorem Equation3907_implies_Equation4096 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq51 eq14


@[equational_result]
theorem Equation3907_implies_Equation4091 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq51 eq14


@[equational_result]
theorem Equation3907_implies_Equation4069 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK2) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq51 eq14


@[equational_result]
theorem Equation3907_implies_Equation3690 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation3907_implies_Equation4067 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq51 eq14


@[equational_result]
theorem Equation3907_implies_Equation4597 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4597 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq51 eq14


@[equational_result]
theorem Equation3907_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3663 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation3907_implies_Equation4608 (G : Type*) [Magma G] (h : Equation3907 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq51 (X0 : G) : (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq51 eq14


