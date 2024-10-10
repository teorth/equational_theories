import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation1878_implies_Equation216 (G : Type*) [Magma G] (h : Equation1878 G) : Equation216 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq41 (X0 X1 : G) : sK0 ≠ ((sK0 ◇ (X0 ◇ X1)) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  subsumption eq41 eq18


@[equational_result]
theorem Equation1879_implies_Equation162 (G : Type*) [Magma G] (h : Equation1879 G) : Equation162 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation1879_implies_Equation3326 (G : Type*) [Magma G] (h : Equation1879 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq45 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq45 rfl


@[equational_result]
theorem Equation1879_implies_Equation4134 (G : Type*) [Magma G] (h : Equation1879 G) : Equation4134 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X0) = (((X3 ◇ X0) ◇ X4) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq73 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq73 rfl


@[equational_result]
theorem Equation1882_implies_Equation1466 (G : Type*) [Magma G] (h : Equation1882 G) : Equation1466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X5)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq37 (X0 : G) : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq37 eq16


@[equational_result]
theorem Equation1886_implies_Equation2108 (G : Type*) [Magma G] (h : Equation1886 G) : Equation2108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq11 -- backward demodulation 11,12
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq16 eq15 -- backward demodulation 15,16
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq16 eq18 -- forward demodulation 18,16
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq23 eq19 -- backward demodulation 19,23
  have eq27 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq24 eq14 -- backward demodulation 14,24
  have eq29 : sK0 ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq24 eq27 -- forward demodulation 27,24
  have eq31 : sK0 ≠ (sK2 ◇ sK1) := superpose eq24 eq29 -- forward demodulation 29,24
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq30 eq24 -- superposition 24,30, 30 into 24, unify on (0).2 in 30 and (0).1 in 24
  have eq34 : sK0 ≠ sK1 := superpose eq24 eq31 -- superposition 31,24, 24 into 31, unify on (0).2 in 24 and (0).2 in 31
  subsumption eq34 eq33


@[equational_result]
theorem Equation1887_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1887 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation1890_implies_Equation2217 (G : Type*) [Magma G] (h : Equation1890 G) : Equation2217 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq30 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq43 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).1.2 in 30
  have eq48 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK1 ◇ sK0)) := superpose eq43 eq10 -- backward demodulation 10,43
  have eq49 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK0)) := superpose eq43 eq48 -- forward demodulation 48,43
  subsumption eq49 eq30


@[equational_result]
theorem Equation1896_implies_Equation776 (G : Type*) [Magma G] (h : Equation1896 G) : Equation776 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK2))) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq14 -- backward demodulation 14,17
  have eq24 : sK0 ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq19 eq12 -- superposition 12,19, 19 into 12, unify on (0).2 in 19 and (0).1.2 in 12
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq47 eq19 -- backward demodulation 19,47
  have eq54 : sK0 ≠ (sK1 ◇ sK2) := superpose eq47 eq24 -- backward demodulation 24,47
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq49 eq47 -- superposition 47,49, 49 into 47, unify on (0).2 in 49 and (0).1 in 47
  have eq58 : sK0 ≠ sK1 := superpose eq47 eq54 -- superposition 54,47, 47 into 54, unify on (0).2 in 47 and (0).2 in 54
  subsumption eq58 eq56


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
theorem Equation1904_implies_Equation1055 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq312 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq266 eq10 -- backward demodulation 10,266
  subsumption eq312 eq12


@[equational_result]
theorem Equation1904_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq12


@[equational_result]
theorem Equation1904_implies_Equation1687 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq377 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq339 eq10 -- backward demodulation 10,339
  subsumption eq377 eq14


@[equational_result]
theorem Equation1904_implies_Equation1701 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq49 eq10 -- backward demodulation 10,49
  subsumption eq56 eq14


@[equational_result]
theorem Equation1904_implies_Equation1958 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1958 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq15 (X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X1) ◇ X4)) = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).1.2 in 15
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq383 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq14 eq339 -- superposition 339,14, 14 into 339, unify on (0).2 in 14 and (0).2.1 in 339
  have eq453 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq383 eq138 -- backward demodulation 138,383
  have eq548 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq453 eq9 -- superposition 9,453, 453 into 9, unify on (0).2 in 453 and (0).1.1.2 in 9
  have eq804 : sK0 ≠ sK0 := superpose eq548 eq10 -- superposition 10,548, 548 into 10, unify on (0).2 in 548 and (0).2 in 10
  subsumption eq804 rfl


@[equational_result]
theorem Equation1904_implies_Equation3353 (G : Type*) [Magma G] (h : Equation1904 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq15 (X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X1) ◇ X4)) = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4)))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq95 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq15 -- superposition 15,14, 14 into 15, unify on (0).2 in 14 and (0).1.2 in 15
  have eq339 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq95 -- superposition 95,9, 9 into 95, unify on (0).2 in 9 and (0).2.1 in 95
  have eq383 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq14 eq339 -- superposition 339,14, 14 into 339, unify on (0).2 in 14 and (0).2.1 in 339
  have eq453 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq383 eq138 -- backward demodulation 138,383
  have eq556 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq453 eq10 -- superposition 10,453, 453 into 10, unify on (0).2 in 453 and (0).2 in 10
  subsumption eq556 rfl


@[equational_result]
theorem Equation1904_implies_Equation364 (G : Type*) [Magma G] (h : Equation1904 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq130 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- superposition 10,49, 49 into 10, unify on (0).2 in 49 and (0).2 in 10
  subsumption eq130 rfl


@[equational_result]
theorem Equation1904_implies_Equation3897 (G : Type*) [Magma G] (h : Equation1904 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).1.2 in 9
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq20 eq38 -- superposition 38,20, 20 into 38, unify on (0).2 in 20 and (0).2.1.2 in 38
  have eq644 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq266 eq10 -- superposition 10,266, 266 into 10, unify on (0).2 in 266 and (0).2 in 10
  subsumption eq644 rfl


@[equational_result]
theorem Equation1904_implies_Equation4642 (G : Type*) [Magma G] (h : Equation1904 G) : Equation4642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK2 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq14 eq20 -- superposition 20,14, 14 into 20, unify on (0).2 in 14 and (0).2.2 in 20
  have eq56 : ((sK0 ◇ sK1) ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq49 eq10 -- backward demodulation 10,49
  have eq81 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq14 eq18 -- superposition 18,14, 14 into 18, unify on (0).2 in 14 and (0).2.2 in 18
  have eq385 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq81 -- superposition 81,9, 9 into 81, unify on (0).2 in 9 and (0).2.1 in 81
  have eq479 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq385 eq56 -- superposition 56,385, 385 into 56, unify on (0).2 in 385 and (0).1 in 56
  subsumption eq479 rfl


@[equational_result]
theorem Equation1905_implies_Equation471 (G : Type*) [Magma G] (h : Equation1905 G) : Equation471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq23 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := superpose eq18 eq10 -- backward demodulation 10,18
  have eq26 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2 in 9
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.1 in 9
  have eq86 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.1 in 13
  have eq107 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq94 -- forward demodulation 94,26
  have eq108 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq107 eq86 -- backward demodulation 86,107
  have eq110 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq107 eq29 -- backward demodulation 29,107
  have eq113 : sK0 ≠ (sK1 ◇ sK0) := superpose eq107 eq23 -- backward demodulation 23,107
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq110 eq108 -- backward demodulation 108,110
  have eq121 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq117 eq9 -- backward demodulation 9,117
  have eq156 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq117 eq121 -- forward demodulation 121,117
  have eq157 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq117 eq156 -- forward demodulation 156,117
  subsumption eq113 eq157


@[equational_result]
theorem Equation1912_implies_Equation1816 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1816 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.2 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.2 in 14
  have eq49 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK0)) := superpose eq36 eq10 -- backward demodulation 10,36
  subsumption eq49 eq17


@[equational_result]
theorem Equation1923_implies_Equation1369 (G : Type*) [Magma G] (h : Equation1923 G) : Equation1369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK0) ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 X3 X4 : G) : (((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X4)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1 in 11
  have eq17 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X3 ◇ (X3 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq15 eq18 -- forward demodulation 18,15
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq25 eq9 -- backward demodulation 9,25
  have eq30 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq25 eq12 -- backward demodulation 12,25
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq25 eq24 -- backward demodulation 24,25
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq25 eq30 -- forward demodulation 30,25
  have eq44 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq32 eq29 -- superposition 29,32, 32 into 29, unify on (0).2 in 32 and (0).1.1 in 29
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq44 eq25 -- backward demodulation 25,44
  have eq50 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq45 eq33 -- backward demodulation 33,45
  have eq55 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK3)) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq59 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq45 eq50 -- forward demodulation 50,45
  subsumption eq55 eq59


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
theorem Equation1942_implies_Equation2914 (G : Type*) [Magma G] (h : Equation1942 G) : Equation2914 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ X2) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2 in 11
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq32 eq34 -- forward demodulation 34,32
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq41 eq19 -- backward demodulation 19,41
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq42 eq21 -- backward demodulation 21,42
  have eq50 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ X2) := superpose eq23 eq49 -- forward demodulation 49,23
  have eq73 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq51 eq12 -- superposition 12,51, 51 into 12, unify on (0).2 in 51 and (0).1.1.2 in 12
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq51 eq9 -- superposition 9,51, 51 into 9, unify on (0).2 in 51 and (0).1.2 in 9
  have eq117 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq50 eq9 -- superposition 9,50, 50 into 9, unify on (0).2 in 50 and (0).1.2 in 9
  have eq141 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq79 eq117 -- forward demodulation 117,79
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq141 eq9 -- backward demodulation 9,141
  have eq145 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq141 eq23 -- backward demodulation 23,141
  have eq161 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq142 eq10 -- backward demodulation 10,142
  have eq162 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq145 eq73 -- backward demodulation 73,145
  have eq166 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq145 eq162 -- forward demodulation 162,145
  have eq169 (X2 X3 : G) : X2 = X3 := superpose eq166 eq166 -- superposition 166,166, 166 into 166, unify on (0).2 in 166 and (0).1 in 166
  have eq177 (X0 : G) : sK0 ≠ (X0 ◇ sK2) := superpose eq166 eq161 -- superposition 161,166, 166 into 161, unify on (0).2 in 166 and (0).2.1 in 161
  subsumption eq177 eq169


@[equational_result]
theorem Equation1945_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1945 G) : Equation1067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq22 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq61 : sK0 ≠ (sK0 ◇ (sK3 ◇ sK0)) := superpose eq22 eq10 -- backward demodulation 10,22
  subsumption eq61 eq22


@[equational_result]
theorem Equation1945_implies_Equation2111 (G : Type*) [Magma G] (h : Equation1945 G) : Equation2111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq13 eq12 -- backward demodulation 12,13
  have eq22 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1 in 21
  have eq30 (X0 : G) : sK0 ≠ ((X0 ◇ sK2) ◇ (sK1 ◇ sK0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1 in 10
  subsumption eq30 eq22


@[equational_result]
theorem Equation1949_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1949_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


@[equational_result]
theorem Equation1949_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1184 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq76 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq76 rfl


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
theorem Equation1962_implies_Equation1115 (G : Type*) [Magma G] (h : Equation1962 G) : Equation1115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X2 : G) : (X2 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1 in 12
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2 in 11
  have eq35 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).2.2 in 11
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq35 eq29 -- backward demodulation 29,35
  have eq44 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X2) ◇ X2) := superpose eq43 eq27 -- backward demodulation 27,43
  have eq48 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose eq44 eq10 -- backward demodulation 10,44
  have eq49 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq35 eq48 -- forward demodulation 48,35
  have eq51 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq44 eq44 -- superposition 44,44, 44 into 44, unify on (0).2 in 44 and (0).2 in 44
  have eq113 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = X2 := superpose eq9 eq51 -- superposition 51,9, 9 into 51, unify on (0).2 in 9 and (0).1 in 51
  have eq143 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ sK0)) := superpose eq51 eq49 -- superposition 49,51, 51 into 49, unify on (0).2 in 51 and (0).2.2 in 49
  subsumption eq143 eq113


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
theorem Equation1976_implies_Equation2983 (G : Type*) [Magma G] (h : Equation1976 G) : Equation2983 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X2)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X0) ◇ X2) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq33 (X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X1)) = (X1 ◇ (X4 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq44 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq9 eq33 -- superposition 33,9, 9 into 33, unify on (0).2 in 9 and (0).1.2 in 33
  have eq49 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X1))) = (X0 ◇ (X4 ◇ X0)) := superpose eq12 eq33 -- superposition 33,12, 12 into 33, unify on (0).2 in 12 and (0).1.2 in 33
  have eq65 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq33 eq11 -- superposition 11,33, 33 into 11, unify on (0).2 in 33 and (0).1.2 in 11
  have eq123 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1 in 13
  have eq139 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq44 eq123 -- forward demodulation 123,44
  have eq150 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq33 eq139 -- superposition 139,33, 33 into 139, unify on (0).2 in 33 and (0).1.2 in 139
  have eq162 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq150 eq13 -- backward demodulation 13,150
  have eq176 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = (X0 ◇ X3) := superpose eq162 eq49 -- backward demodulation 49,162
  have eq177 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq162 eq65 -- backward demodulation 65,162
  have eq199 : sK0 ≠ ((sK2 ◇ sK2) ◇ sK2) := superpose eq162 eq10 -- backward demodulation 10,162
  have eq200 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq177 eq15 -- backward demodulation 15,177
  have eq205 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq200 eq176 -- backward demodulation 176,200
  have eq207 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq205 eq177 -- backward demodulation 177,205
  have eq209 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq205 eq207 -- forward demodulation 207,205
  subsumption eq199 eq209


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
theorem Equation1979_implies_Equation1133 (G : Type*) [Magma G] (h : Equation1979 G) : Equation1133 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq28 eq14 -- backward demodulation 14,28
  have eq38 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq28 eq10 -- backward demodulation 10,28
  subsumption eq38 eq34


@[equational_result]
theorem Equation1983_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1038 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1983_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


@[equational_result]
theorem Equation1983_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1171 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq87 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq87 rfl


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
theorem Equation2000_implies_Equation1035 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2000_implies_Equation1085 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2000_implies_Equation1167 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq19 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  subsumption eq19 eq12


@[equational_result]
theorem Equation2010_implies_Equation913 (G : Type*) [Magma G] (h : Equation2010 G) : Equation913 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK1 ◇ sK2) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1 in 11
  have eq22 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq12 -- backward demodulation 12,16
  have eq23 (X3 X4 : G) : X3 = X4 := superpose eq9 eq22 -- superposition 22,9, 9 into 22, unify on (0).2 in 9 and (0).1 in 22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq14 -- superposition 14,22, 22 into 14, unify on (0).2 in 22 and (0).2 in 14
  subsumption eq34 eq23


@[equational_result]
theorem Equation2039_implies_Equation267 (G : Type*) [Magma G] (h : Equation2039 G) : Equation267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X3 : G) : (((X3 ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq26 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1 in 12
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).2 in 37
  have eq120 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq37 eq13 -- superposition 13,37, 37 into 13, unify on (0).2 in 37 and (0).2.1 in 13
  have eq204 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ X0) := superpose eq172 eq120 -- backward demodulation 120,172
  subsumption eq204 eq12


@[equational_result]
theorem Equation204_implies_Equation1846 (G : Type*) [Magma G] (h : Equation204 G) : Equation1846 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK3)) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq9


@[equational_result]
theorem Equation2042_implies_Equation2893 (G : Type*) [Magma G] (h : Equation2042 G) : Equation2893 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1 in 12
  have eq36 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq26 -- forward demodulation 26,9
  have eq40 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq36 eq12 -- superposition 12,36, 36 into 12, unify on (0).2 in 36 and (0).2.1.1 in 12
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq40 eq40 -- superposition 40,40, 40 into 40, unify on (0).2 in 40 and (0).1 in 40
  have eq55 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq40 eq11 -- superposition 11,40, 40 into 11, unify on (0).2 in 40 and (0).2.2 in 11
  have eq56 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq40 eq9 -- superposition 9,40, 40 into 9, unify on (0).2 in 40 and (0).1.1 in 9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq40 eq12 -- superposition 12,40, 40 into 12, unify on (0).2 in 40 and (0).2.1 in 12
  have eq107 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq50 -- superposition 50,9, 9 into 50, unify on (0).2 in 9 and (0).1.1 in 50
  have eq114 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq50 eq50 -- superposition 50,50, 50 into 50, unify on (0).2 in 50 and (0).1.1 in 50
  have eq161 (X0 X1 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq107 -- forward demodulation 107,11
  have eq162 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq161 eq57 -- backward demodulation 57,161
  have eq167 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq56 eq114 -- forward demodulation 114,56
  have eq206 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq55 -- superposition 55,9, 9 into 55, unify on (0).2 in 9 and (0).2.2.1 in 55
  have eq215 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq50 eq55 -- superposition 55,50, 50 into 55, unify on (0).2 in 50 and (0).2.2.1 in 55
  have eq236 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq206 -- forward demodulation 206,9
  have eq238 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X3) ◇ X0) := superpose eq236 eq12 -- backward demodulation 12,236
  have eq241 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq56 eq215 -- forward demodulation 215,56
  have eq242 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq241 eq32 -- backward demodulation 32,241
  have eq246 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq167 eq242 -- forward demodulation 242,167
  have eq247 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq9 eq246 -- forward demodulation 246,9
  have eq271 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq238 -- superposition 238,9, 9 into 238, unify on (0).2 in 9 and (0).2.1 in 238
  have eq339 (X0 X1 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) := superpose eq11 eq271 -- forward demodulation 271,11
  have eq340 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq236 eq339 -- forward demodulation 339,236
  have eq341 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK3) := superpose eq340 eq10 -- backward demodulation 10,340
  have eq342 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK3) := superpose eq162 eq341 -- forward demodulation 341,162
  subsumption eq342 eq247


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
theorem Equation2047_implies_Equation268 (G : Type*) [Magma G] (h : Equation2047 G) : Equation268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X3 X4 : G) : (((X3 ◇ X3) ◇ X0) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq18 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK2) := superpose eq18 eq10 -- backward demodulation 10,18
  subsumption eq23 eq16


@[equational_result]
theorem Equation2048_implies_Equation2668 (G : Type*) [Magma G] (h : Equation2048 G) : Equation2668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq25 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK3) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq26 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK3) := superpose eq16 eq25 -- forward demodulation 25,16
  subsumption eq26 eq13


@[equational_result]
theorem Equation2052_implies_Equation3513 (G : Type*) [Magma G] (h : Equation2052 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2053_implies_Equation3253 (G : Type*) [Magma G] (h : Equation2053 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation2054_implies_Equation307 (G : Type*) [Magma G] (h : Equation2054 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2055_implies_Equation2656 (G : Type*) [Magma G] (h : Equation2055 G) : Equation2656 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1.1 in 9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq38 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).1.1.1 in 13
  have eq80 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq38 eq13 -- superposition 13,38, 38 into 13, unify on (0).2 in 38 and (0).1.1 in 13
  have eq86 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.1.1 in 9
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq86 -- forward demodulation 86,9
  have eq95 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq94 -- forward demodulation 94,12
  have eq136 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq80 eq11 -- superposition 11,80, 80 into 11, unify on (0).2 in 80 and (0).1.1 in 11
  have eq148 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq149 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq95 eq148 -- forward demodulation 148,95
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq149 eq22 -- backward demodulation 22,149
  have eq166 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq158 eq13 -- backward demodulation 13,158
  have eq194 : sK0 ≠ sK0 := superpose eq166 eq10 -- superposition 10,166, 166 into 10, unify on (0).2 in 166 and (0).2 in 10
  subsumption eq194 rfl


@[equational_result]
theorem Equation2055_implies_Equation308 (G : Type*) [Magma G] (h : Equation2055 G) : Equation308 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


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
theorem Equation2057_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2057 G) : Equation2682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2 in 12
  have eq27 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1.2 in 13
  have eq67 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1 in 10
  have eq260 : sK0 ≠ sK0 := superpose eq27 eq67 -- superposition 67,27, 27 into 67, unify on (0).2 in 27 and (0).2 in 67
  subsumption eq260 rfl


@[equational_result]
theorem Equation2058_implies_Equation2695 (G : Type*) [Magma G] (h : Equation2058 G) : Equation2695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq81 (X0 X3 : G) : (X3 ◇ X3) = (X3 ◇ X0) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq114 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq81 eq11 -- backward demodulation 11,81
  have eq115 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK4) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq121 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK4) := superpose eq81 eq115 -- forward demodulation 115,81
  have eq127 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1 in 81
  have eq156 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq9 eq127 -- superposition 127,9, 9 into 127, unify on (0).2 in 9 and (0).1 in 127
  have eq274 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK4) := superpose eq114 eq121 -- superposition 121,114, 114 into 121, unify on (0).2 in 114 and (0).2.1 in 121
  subsumption eq274 eq156


@[equational_result]
theorem Equation2059_implies_Equation2657 (G : Type*) [Magma G] (h : Equation2059 G) : Equation2657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X4) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1 in 13
  have eq72 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) ◇ X0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq72 eq39


@[equational_result]
theorem Equation2061_implies_Equation255 (G : Type*) [Magma G] (h : Equation2061 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq14 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq80 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.1.1.2 in 12
  have eq93 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq80 -- forward demodulation 80,12
  have eq94 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq14 eq93 -- forward demodulation 93,14
  have eq95 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq94 -- forward demodulation 94,10
  have eq106 : sK0 ≠ sK0 := superpose eq95 eq9 -- superposition 9,95, 95 into 9, unify on (0).2 in 95 and (0).2 in 9
  subsumption eq106 rfl


@[equational_result]
theorem Equation2061_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2061 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq12 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq14 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1.1 in 10
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq63 -- forward demodulation 63,10
  have eq70 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq68 eq9 -- backward demodulation 9,68
  have eq91 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq32 eq12 -- superposition 12,32, 32 into 12, unify on (0).2 in 32 and (0).1.1.1.2 in 12
  have eq105 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq91 -- forward demodulation 91,12
  have eq106 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq14 eq105 -- forward demodulation 105,14
  have eq107 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq70 -- superposition 70,107, 107 into 70, unify on (0).2 in 107 and (0).2 in 70
  subsumption eq117 rfl


@[equational_result]
theorem Equation2061_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2061 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose eq10 eq9 -- backward demodulation 9,10
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq15 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1 in 8
  have eq33 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq12 -- superposition 12,8, 8 into 12, unify on (0).2 in 8 and (0).2 in 12
  have eq91 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq33 eq13 -- superposition 13,33, 33 into 13, unify on (0).2 in 33 and (0).1.1.1.2 in 13
  have eq105 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq91 -- forward demodulation 91,13
  have eq106 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq15 eq105 -- forward demodulation 105,15
  have eq107 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq106 -- forward demodulation 106,10
  have eq117 : sK0 ≠ sK0 := superpose eq107 eq11 -- superposition 11,107, 107 into 11, unify on (0).2 in 107 and (0).2 in 11
  subsumption eq117 rfl


@[equational_result]
theorem Equation2061_implies_Equation307 (G : Type*) [Magma G] (h : Equation2061 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq58 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq32 eq9 -- superposition 9,32, 32 into 9, unify on (0).2 in 32 and (0).2 in 9
  subsumption eq58 rfl


@[equational_result]
theorem Equation2061_implies_Equation3456 (G : Type*) [Magma G] (h : Equation2061 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.1 in 8
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1 in 10
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq10 eq8 -- superposition 8,10, 10 into 8, unify on (0).2 in 10 and (0).1.1.1 in 8
  have eq32 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq60 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq32 eq15 -- superposition 15,32, 32 into 15, unify on (0).2 in 32 and (0).1 in 15
  have eq65 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq60 -- forward demodulation 60,10
  have eq66 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq65 -- forward demodulation 65,8
  have eq137 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq66 eq9 -- superposition 9,66, 66 into 9, unify on (0).2 in 66 and (0).2 in 9
  subsumption eq137 rfl


@[equational_result]
theorem Equation206_implies_Equation1426 (G : Type*) [Magma G] (h : Equation206 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq54 rfl


@[equational_result]
theorem Equation206_implies_Equation151 (G : Type*) [Magma G] (h : Equation206 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq18 -- forward demodulation 18,13
  have eq38 : sK0 ≠ sK0 := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq38 rfl


@[equational_result]
theorem Equation206_implies_Equation1832 (G : Type*) [Magma G] (h : Equation206 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose eq13 eq9 -- backward demodulation 9,13
  have eq19 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1.2 in 8
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq19 -- forward demodulation 19,13
  have eq54 : sK0 ≠ sK0 := superpose eq20 eq15 -- superposition 15,20, 20 into 15, unify on (0).2 in 20 and (0).2 in 15
  subsumption eq54 rfl


@[equational_result]
theorem Equation206_implies_Equation2238 (G : Type*) [Magma G] (h : Equation206 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq15 eq8


@[equational_result]
theorem Equation206_implies_Equation23 (G : Type*) [Magma G] (h : Equation206 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).1.1 in 8
  have eq22 : sK0 ≠ sK0 := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2 in 9
  subsumption eq22 rfl


@[equational_result]
theorem Equation2062_implies_Equation4598 (G : Type*) [Magma G] (h : Equation2062 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq27 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq32 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq9 eq27 -- forward demodulation 27,9
  have eq85 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ X3) := superpose eq24 eq24 -- superposition 24,24, 24 into 24, unify on (0).2 in 24 and (0).2 in 24
  have eq125 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq32 eq85 -- superposition 85,32, 32 into 85, unify on (0).2 in 32 and (0).1 in 85
  have eq362 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq125 eq9 -- superposition 9,125, 125 into 9, unify on (0).2 in 125 and (0).1.2 in 9
  have eq364 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq125 eq85 -- superposition 85,125, 125 into 85, unify on (0).2 in 125 and (0).1.1 in 85
  have eq373 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq364 eq362 -- backward demodulation 362,364
  have eq1084 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq373 eq10 -- superposition 10,373, 373 into 10, unify on (0).2 in 373 and (0).2 in 10
  subsumption eq1084 rfl


@[equational_result]
theorem Equation206_implies_Equation307 (G : Type*) [Magma G] (h : Equation206 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2.1 in 10
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation2065_implies_Equation2676 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq101 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := superpose eq13 eq12 -- superposition 12,13, 13 into 12, unify on (0).2 in 13 and (0).1.1.1 in 12
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X5)) := superpose eq13 eq48 -- superposition 48,13, 13 into 48, unify on (0).2 in 13 and (0).1 in 48
  have eq264 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.1 in 17
  have eq290 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq17 eq19 -- superposition 19,17, 17 into 19, unify on (0).2 in 17 and (0).1.1.1 in 19
  have eq305 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X5)) := superpose eq264 eq163 -- backward demodulation 163,264
  have eq312 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) := superpose eq9 eq305 -- forward demodulation 305,9
  have eq321 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq312 eq72 -- backward demodulation 72,312
  have eq357 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq312 eq290 -- forward demodulation 290,312
  have eq358 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq357 eq321 -- backward demodulation 321,357
  have eq362 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq358 eq101 -- backward demodulation 101,358
  have eq399 : sK0 ≠ sK0 := superpose eq362 eq10 -- superposition 10,362, 362 into 10, unify on (0).2 in 362 and (0).2 in 10
  subsumption eq399 rfl


@[equational_result]
theorem Equation2065_implies_Equation4357 (G : Type*) [Magma G] (h : Equation2065 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).1.1 in 9
  have eq207 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq48 eq10 -- superposition 10,48, 48 into 10, unify on (0).2 in 48 and (0).2 in 10
  subsumption eq207 eq48


@[equational_result]
theorem Equation2066_implies_Equation3326 (G : Type*) [Magma G] (h : Equation2066 G) : Equation3326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X0) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1.1 in 13
  have eq140 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).2 in 17
  have eq207 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq140 eq9 -- superposition 9,140, 140 into 9, unify on (0).2 in 140 and (0).1.1 in 9
  have eq296 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq207 eq10 -- superposition 10,207, 207 into 10, unify on (0).2 in 207 and (0).2 in 10
  subsumption eq296 rfl


@[equational_result]
theorem Equation2067_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2067 G) : Equation2689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq21 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ X1) ◇ X0) = X3 := superpose eq13 eq12 -- backward demodulation 12,13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq21 eq21 -- superposition 21,21, 21 into 21, unify on (0).2 in 21 and (0).1.1 in 21
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq24 eq21 -- superposition 21,24, 24 into 21, unify on (0).2 in 24 and (0).1.1.1 in 21
  have eq42 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK2) := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2.1 in 10
  subsumption eq42 eq36


@[equational_result]
theorem Equation2069_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2069 G) : Equation2690 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq13 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X5) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq69 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq17 eq13 -- superposition 13,17, 17 into 13, unify on (0).2 in 17 and (0).1.1.1 in 13
  have eq75 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK3) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.1 in 10
  subsumption eq75 eq69


@[equational_result]
theorem Equation2071_implies_Equation2898 (G : Type*) [Magma G] (h : Equation2071 G) : Equation2898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X5) ◇ (X0 ◇ X1)) = (((X0 ◇ X3) ◇ X0) ◇ X4) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq37 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK0) ◇ sK4) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1 in 10
  have eq46 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ X4) = X0 := superpose eq9 eq21 -- forward demodulation 21,9
  subsumption eq37 eq46


@[equational_result]
theorem Equation2072_implies_Equation2067 (G : Type*) [Magma G] (h : Equation2072 G) : Equation2067 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2.2 in 12
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq52 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ X3) ◇ X1) := superpose eq30 eq30 -- superposition 30,30, 30 into 30, unify on (0).2 in 30 and (0).2 in 30
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq118 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ X3) := superpose eq9 eq52 -- superposition 52,9, 9 into 52, unify on (0).2 in 9 and (0).1.1 in 52
  have eq168 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ (sK2 ◇ sK1)) := superpose eq52 eq10 -- superposition 10,52, 52 into 10, unify on (0).2 in 52 and (0).2 in 10
  have eq203 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq118 eq16 -- backward demodulation 16,118
  have eq226 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq73 eq203 -- forward demodulation 203,73
  subsumption eq168 eq226


@[equational_result]
theorem Equation2073_implies_Equation2684 (G : Type*) [Magma G] (h : Equation2073 G) : Equation2684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq21 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq43 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ X0) ◇ sK1) := superpose eq16 eq21 -- superposition 21,16, 16 into 21, unify on (0).2 in 16 and (0).2.1 in 21
  subsumption eq43 eq28


@[equational_result]
theorem Equation2074_implies_Equation2082 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK3 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation2075_implies_Equation2072 (G : Type*) [Magma G] (h : Equation2075 G) : Equation2072 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq21 (X0 : G) : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq21 eq13


@[equational_result]
theorem Equation2076_implies_Equation2688 (G : Type*) [Magma G] (h : Equation2076 G) : Equation2688 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq1374 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq30 eq10 -- superposition 10,30, 30 into 10, unify on (0).2 in 30 and (0).2 in 10
  subsumption eq1374 eq17


@[equational_result]
theorem Equation2076_implies_Equation3323 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq480 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq33 eq159 -- superposition 159,33, 33 into 159, unify on (0).2 in 33 and (0).2.2 in 159
  have eq2556 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq480 eq10 -- superposition 10,480, 480 into 10, unify on (0).2 in 480 and (0).2 in 10
  subsumption eq2556 rfl


@[equational_result]
theorem Equation2076_implies_Equation3334 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq490 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq159 eq12 -- superposition 12,159, 159 into 12, unify on (0).2 in 159 and (0).2.2 in 12
  have eq644 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := superpose eq490 eq10 -- backward demodulation 10,490
  subsumption eq644 eq12


@[equational_result]
theorem Equation2076_implies_Equation3526 (G : Type*) [Magma G] (h : Equation2076 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq488 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq159 eq10 -- superposition 10,159, 159 into 10, unify on (0).2 in 159 and (0).2 in 10
  subsumption eq488 rfl


@[equational_result]
theorem Equation2076_implies_Equation4358 (G : Type*) [Magma G] (h : Equation2076 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq490 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq159 eq12 -- superposition 12,159, 159 into 12, unify on (0).2 in 159 and (0).2.2 in 12
  have eq3858 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq490 eq10 -- superposition 10,490, 490 into 10, unify on (0).2 in 490 and (0).2 in 10
  subsumption eq3858 rfl


@[equational_result]
theorem Equation2076_implies_Equation4673 (G : Type*) [Magma G] (h : Equation2076 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.2 in 12
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq16 -- superposition 16,17, 17 into 16, unify on (0).2 in 17 and (0).2.2 in 16
  have eq481 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq159 -- superposition 159,11, 11 into 159, unify on (0).2 in 11 and (0).2 in 159
  have eq3053 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose eq481 eq10 -- superposition 10,481, 481 into 10, unify on (0).2 in 481 and (0).2 in 10
  subsumption eq3053 rfl


@[equational_result]
theorem Equation2077_implies_Equation2874 (G : Type*) [Magma G] (h : Equation2077 G) : Equation2874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X1)) ◇ sK0) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2080_implies_Equation2039 (G : Type*) [Magma G] (h : Equation2080 G) : Equation2039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (X3 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq32 (X0 : G) : sK0 ≠ (((sK0 ◇ sK0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq32 eq9


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
theorem Equation2083_implies_Equation2871 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq27 (X0 X1 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X1)) ◇ sK2) ◇ sK3) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq27 eq20


@[equational_result]
theorem Equation2084_implies_Equation267 (G : Type*) [Magma G] (h : Equation2084 G) : Equation267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ (X3 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ (X3 ◇ X2)) ◇ X0) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ X0) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq38 (X0 X4 X5 X6 : G) : (((X4 ◇ X5) ◇ X0) ◇ X6) = X4 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.2 in 13
  have eq67 (X0 : G) : sK0 ≠ (((sK0 ◇ X0) ◇ sK2) ◇ sK1) := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2.1.1 in 10
  subsumption eq67 eq38


@[equational_result]
theorem Equation2085_implies_Equation2851 (G : Type*) [Magma G] (h : Equation2085 G) : Equation2851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X4 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X0) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (((sK0 ◇ (X0 ◇ X0)) ◇ sK1) ◇ sK2) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.1.1 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation209_implies_Equation1426 (G : Type*) [Magma G] (h : Equation209 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation209_implies_Equation1452 (G : Type*) [Magma G] (h : Equation209 G) : Equation1452 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq14 rfl


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
theorem Equation2097_implies_Equation8 (G : Type*) [Magma G] (h : Equation2097 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2098_implies_Equation47 (G : Type*) [Magma G] (h : Equation2098 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq13 rfl


@[equational_result]
theorem Equation2099_implies_Equation673 (G : Type*) [Magma G] (h : Equation2099 G) : Equation673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq16 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq21 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq18 eq11 -- backward demodulation 11,18
  have eq24 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq15 eq21 -- forward demodulation 21,15
  have eq25 : sK0 ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq24 eq10 -- backward demodulation 10,24
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq24 -- superposition 24,12, 12 into 24, unify on (0).2 in 12 and (0).2.2 in 24
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq31 -- forward demodulation 31,12
  have eq37 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq35 eq18 -- backward demodulation 18,35
  have eq39 : sK0 ≠ (sK1 ◇ sK0) := superpose eq35 eq25 -- backward demodulation 25,35
  have eq43 (X1 X2 : G) : X1 = X2 := superpose eq37 eq37 -- superposition 37,37, 37 into 37, unify on (0).2 in 37 and (0).1 in 37
  have eq51 (X0 : G) : sK0 ≠ (X0 ◇ X0) := superpose eq37 eq39 -- superposition 39,37, 37 into 39, unify on (0).2 in 37 and (0).2 in 39
  subsumption eq51 eq43


@[equational_result]
theorem Equation2101_implies_Equation817 (G : Type*) [Magma G] (h : Equation2101 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation2107_implies_Equation1945 (G : Type*) [Magma G] (h : Equation2107 G) : Equation1945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq12


@[equational_result]
theorem Equation2108_implies_Equation2911 (G : Type*) [Magma G] (h : Equation2108 G) : Equation2911 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X1)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq24 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq17 eq16 -- backward demodulation 16,17
  have eq29 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq27 eq14 -- backward demodulation 14,27
  have eq32 : sK0 ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq27 eq24 -- backward demodulation 24,27
  have eq34 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq27 eq29 -- forward demodulation 29,27
  subsumption eq32 eq34


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
theorem Equation2111_implies_Equation1755 (G : Type*) [Magma G] (h : Equation2111 G) : Equation1755 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq34 (X0 : G) : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK0 ◇ X0) ◇ sK0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq34 eq18


@[equational_result]
theorem Equation2112_implies_Equation995 (G : Type*) [Magma G] (h : Equation2112 G) : Equation995 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq17 (X2 X3 : G) : X2 = X3 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq25 (X0 X1 : G) : sK0 ≠ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq25 eq17


@[equational_result]
theorem Equation2113_implies_Equation1334 (G : Type*) [Magma G] (h : Equation2113 G) : Equation1334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK2) ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).2.1 in 30
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq30 eq9 -- superposition 9,30, 30 into 9, unify on (0).2 in 30 and (0).1.1 in 9
  have eq57 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq44 eq33 -- backward demodulation 33,44
  have eq87 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := superpose eq45 eq10 -- backward demodulation 10,45
  have eq98 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq49 eq87 -- backward demodulation 87,49
  subsumption eq98 eq57


@[equational_result]
theorem Equation212_implies_Equation160 (G : Type*) [Magma G] (h : Equation212 G) : Equation160 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation2130_implies_Equation2144 (G : Type*) [Magma G] (h : Equation2130 G) : Equation2144 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 X2 X3 : G) : (X2 ◇ X1) = (((X3 ◇ X3) ◇ (X2 ◇ X1)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq13 -- superposition 13,11, 11 into 13, unify on (0).2 in 11 and (0).2.1 in 13
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq26 -- forward demodulation 26,11
  have eq35 : sK0 ≠ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := superpose eq27 eq10 -- backward demodulation 10,27
  subsumption eq35 eq33


@[equational_result]
theorem Equation2140_implies_Equation169 (G : Type*) [Magma G] (h : Equation2140 G) : Equation169 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X1 ◇ X2) = (((X3 ◇ X3) ◇ X3) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq39 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq39 rfl


@[equational_result]
theorem Equation2144_implies_Equation2222 (G : Type*) [Magma G] (h : Equation2144 G) : Equation2222 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq21 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK2 ◇ sK0)) := superpose eq16 eq10 -- backward demodulation 10,16
  have eq22 : sK0 ≠ ((sK3 ◇ sK3) ◇ (sK0 ◇ sK0)) := superpose eq16 eq21 -- forward demodulation 21,16
  subsumption eq22 eq12


@[equational_result]
theorem Equation2148_implies_Equation1945 (G : Type*) [Magma G] (h : Equation2148 G) : Equation1945 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq20 : sK0 ≠ (sK2 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq20 eq14


@[equational_result]
theorem Equation215_implies_Equation1430 (G : Type*) [Magma G] (h : Equation215 G) : Equation1430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation215_implies_Equation1457 (G : Type*) [Magma G] (h : Equation215 G) : Equation1457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation215_implies_Equation4357 (G : Type*) [Magma G] (h : Equation215 G) : Equation4357 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq21 (X0 X1 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ X5)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2.1 in 12
  have eq87 (X0 : G) : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ X0)) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq87 eq21


@[equational_result]
theorem Equation2162_implies_Equation1428 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1479 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1482 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation2162_implies_Equation1485 (G : Type*) [Magma G] (h : Equation2162 G) : Equation1485 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq16 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ (X2 ◇ X3))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2.1 in 11
  have eq50 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq50 rfl


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
theorem Equation2165_implies_Equation1697 (G : Type*) [Magma G] (h : Equation2165 G) : Equation1697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq80 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq138 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).1.1 in 9
  have eq499 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq12 eq80 -- superposition 80,12, 12 into 80, unify on (0).2 in 12 and (0).2.1 in 80
  have eq537 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq138 eq499 -- forward demodulation 499,138
  have eq570 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq537 eq28 -- superposition 28,537, 537 into 28, unify on (0).2 in 537 and (0).1.2.1 in 28
  have eq1675 : sK0 ≠ sK0 := superpose eq570 eq10 -- superposition 10,570, 570 into 10, unify on (0).2 in 570 and (0).2 in 10
  subsumption eq1675 rfl


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
theorem Equation2169_implies_Equation1691 (G : Type*) [Magma G] (h : Equation2169 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq23 (X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq77 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq77 rfl


@[equational_result]
theorem Equation2169_implies_Equation1705 (G : Type*) [Magma G] (h : Equation2169 G) : Equation1705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2169_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2169 G) : Equation2090 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq32 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq9 eq18 -- superposition 18,9, 9 into 18, unify on (0).2 in 9 and (0).1 in 18
  have eq138 : sK0 ≠ sK0 := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).2 in 10
  subsumption eq138 rfl


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
theorem Equation2186_implies_Equation1374 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1374 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq17 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq17 eq12


@[equational_result]
theorem Equation2186_implies_Equation1793 (G : Type*) [Magma G] (h : Equation2186 G) : Equation1793 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq12 eq14 -- superposition 14,12, 12 into 14, unify on (0).2 in 12 and (0).2.1.1 in 14
  have eq61 : sK0 ≠ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := superpose eq41 eq10 -- backward demodulation 10,41
  subsumption eq61 eq12


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
theorem Equation219_implies_Equation873 (G : Type*) [Magma G] (h : Equation219 G) : Equation873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq13 rfl


@[equational_result]
theorem Equation2203_implies_Equation1370 (G : Type*) [Magma G] (h : Equation2203 G) : Equation1370 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK2 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq47 : sK0 ≠ sK0 := superpose eq31 eq10 -- superposition 10,31, 31 into 10, unify on (0).2 in 31 and (0).2 in 10
  subsumption eq47 rfl


@[equational_result]
theorem Equation222_implies_Equation118 (G : Type*) [Magma G] (h : Equation222 G) : Equation118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq20 : sK0 ≠ sK0 := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation2222_implies_Equation1890 (G : Type*) [Magma G] (h : Equation2222 G) : Equation1890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X4)) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK2 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq14 eq12


@[equational_result]
theorem Equation222_implies_Equation274 (G : Type*) [Magma G] (h : Equation222 G) : Equation274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2 in 9
  have eq12 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq11 eq10 -- backward demodulation 10,11
  subsumption eq12 eq9


