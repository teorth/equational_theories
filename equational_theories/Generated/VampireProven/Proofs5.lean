import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3907_implies_Equation3890 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK0) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.1.2 in 10
  have eq48 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = ((X4 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1.2 in 9
  have eq57 (X1 X2 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ sK0) := superpose eq14 eq22 -- superposition 22,14, 14 into 22, unify on (0).2 in 14 and (0).2.1.2 in 22
  subsumption eq57 eq48


@[equational_result]
theorem Equation3907_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3661 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation3886_implies_Equation3900 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3900 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK3) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3876 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3876 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3912 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3897 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3901 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3904 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK3) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3868 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3909 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3869 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3886_implies_Equation3899 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3899 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq16 (X1 X3 X5 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ X3) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3886 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3886 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3866 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3866 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3884 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3896 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3903 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3903 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3874 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3874 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3875 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation3900_implies_Equation3913 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3913 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK4) := mod_symm nh
  have eq16 (X2 X4 X5 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X1) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2 in 16
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq18 -- superposition 18,27, 27 into 18, unify on (0).2 in 27 and (0).2 in 18
  subsumption eq58 eq27


@[equational_result]
theorem Equation2623_implies_Equation242 (G : Type*) [Magma G] (h : Equation2623 G) : Equation242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


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
theorem Equation2425_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq94 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq94 rfl


@[equational_result]
theorem Equation2425_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq94 : sK0 ≠ sK0 := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq94 rfl


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
theorem Equation2425_implies_Equation246 (G : Type*) [Magma G] (h : Equation2425 G) : Equation246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2425_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2425_implies_Equation2672 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


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
theorem Equation2425_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2812 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X3)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.2 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


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
theorem Equation3473_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3473_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3499 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3473_implies_Equation3286 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq28 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq28 eq12


@[equational_result]
theorem Equation3473_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3502 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK3)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3473_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq22 (X0 X1 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ (X1 ◇ X1)) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation3473_implies_Equation3464 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3501_implies_Equation3486 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3486 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  have eq53 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq61 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ sK2)) := superpose eq15 eq26 -- superposition 26,15, 15 into 26, unify on (0).2 in 15 and (0).2.2.1 in 26
  subsumption eq61 eq53


@[equational_result]
theorem Equation3501_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3266 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq61 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq61 eq15


@[equational_result]
theorem Equation3501_implies_Equation4276 (G : Type*) [Magma G] (h : Equation3501 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq56 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2 in 10
  subsumption eq56 eq15


@[equational_result]
theorem Equation3501_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3709 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK3)) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq29 eq15


@[equational_result]
theorem Equation3501_implies_Equation3466 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq16 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2.1 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.1 in 10
  subsumption eq29 eq26


@[equational_result]
theorem Equation3501_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3272 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq61 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq61 eq15


@[equational_result]
theorem Equation3486_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK2)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq22


@[equational_result]
theorem Equation3486_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation3486_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq25 eq14


@[equational_result]
theorem Equation3486_implies_Equation3465 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3465 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq25 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ ((X0 ◇ X0) ◇ sK1)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2.1 in 10
  subsumption eq25 eq22


@[equational_result]
theorem Equation3486_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq57 (X0 : G) : (sK0 ◇ sK0) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq57 eq14


@[equational_result]
theorem Equation3486_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3471 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq15 (X2 X3 : G) : (X3 ◇ X3) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.2.1 in 9
  have eq25 (X0 : G) : (X0 ◇ X0) ≠ (sK1 ◇ ((X0 ◇ X0) ◇ sK0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1 in 10
  subsumption eq25 eq22


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
theorem Equation1594_implies_Equation4606 (G : Type*) [Magma G] (h : Equation1594 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq31 eq9 -- superposition 9,31, 31 into 9, unify on (0).2 in 31 and (0).1.2 in 9
  have eq294 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq46 eq10 -- superposition 10,46, 46 into 10, unify on (0).2 in 46 and (0).2 in 10
  subsumption eq294 eq46


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
theorem Equation727_implies_Equation964 (G : Type*) [Magma G] (h : Equation727 G) : Equation964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ (X1 ◇ X3)) ◇ ((X4 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq20 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq47 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.1 in 20
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.2.2 in 20
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).1.2 in 20
  have eq54 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).1.2 in 20
  have eq63 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq22 eq47 -- forward demodulation 47,22
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq54 eq51 -- backward demodulation 51,54
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3))) = X3 := superpose eq65 eq11 -- backward demodulation 11,65
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X4 ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5))) = X5 := superpose eq12 eq66 -- superposition 66,12, 12 into 66, unify on (0).2 in 12 and (0).1.1.2.1 in 66
  have eq98 (X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X4 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) = X5 := superpose eq16 eq78 -- forward demodulation 78,16
  have eq113 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq20 eq53 -- superposition 53,20, 20 into 53, unify on (0).2 in 20 and (0).1.1 in 53
  have eq135 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ sK1) ◇ (sK1 ◇ sK0))) := superpose eq53 eq10 -- superposition 10,53, 53 into 10, unify on (0).2 in 53 and (0).2.2 in 10
  have eq342 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq98 eq9 -- superposition 9,98, 98 into 9, unify on (0).2 in 98 and (0).1.2.2 in 9
  have eq387 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4))) = X4 := superpose eq342 eq63 -- backward demodulation 63,342
  have eq430 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X4 := superpose eq113 eq387 -- forward demodulation 387,113
  have eq523 : sK0 ≠ sK0 := superpose eq430 eq135 -- superposition 135,430, 430 into 135, unify on (0).2 in 430 and (0).2 in 135
  subsumption eq523 rfl


@[equational_result]
theorem Equation727_implies_Equation1454 (G : Type*) [Magma G] (h : Equation727 G) : Equation1454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq20 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq55 : sK0 ≠ sK0 := superpose eq20 eq10 -- superposition 10,20, 20 into 10, unify on (0).2 in 20 and (0).2 in 10
  subsumption eq55 rfl


@[equational_result]
theorem Equation727_implies_Equation1478 (G : Type*) [Magma G] (h : Equation727 G) : Equation1478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq56 : sK0 ≠ sK0 := superpose eq19 eq10 -- superposition 10,19, 19 into 10, unify on (0).2 in 19 and (0).2 in 10
  subsumption eq56 rfl


@[equational_result]
theorem Equation727_implies_Equation832 (G : Type*) [Magma G] (h : Equation727 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = (X1 ◇ (X1 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ (X1 ◇ X3)) ◇ ((X4 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X5)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq16 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2.1 in 12
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X3 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X5)) = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq12 eq14 -- forward demodulation 14,12
  have eq47 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.1 in 19
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2.2 in 19
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).1.2 in 19
  have eq54 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).1.2 in 19
  have eq63 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X4 := superpose eq22 eq47 -- forward demodulation 47,22
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq54 eq51 -- backward demodulation 51,54
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3))) = X3 := superpose eq65 eq11 -- backward demodulation 11,65
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X4 ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5))) = X5 := superpose eq12 eq66 -- superposition 66,12, 12 into 66, unify on (0).2 in 12 and (0).1.1.2.1 in 66
  have eq98 (X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X4 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) = X5 := superpose eq16 eq78 -- forward demodulation 78,16
  have eq113 (X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq19 eq53 -- superposition 53,19, 19 into 53, unify on (0).2 in 19 and (0).1.1 in 53
  have eq147 (X0 : G) : sK0 ≠ (sK0 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq53 eq10 -- superposition 10,53, 53 into 10, unify on (0).2 in 53 and (0).2.2 in 10
  have eq352 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq98 eq9 -- superposition 9,98, 98 into 9, unify on (0).2 in 98 and (0).1.2.2 in 9
  have eq396 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4))) = X4 := superpose eq352 eq63 -- backward demodulation 63,352
  have eq437 (X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X4 := superpose eq113 eq396 -- forward demodulation 396,113
  have eq503 : sK0 ≠ sK0 := superpose eq437 eq147 -- superposition 147,437, 437 into 147, unify on (0).2 in 437 and (0).2 in 147
  subsumption eq503 rfl


@[equational_result]
theorem Equation964_implies_Equation1594 (G : Type*) [Magma G] (h : Equation964 G) : Equation1594 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq28 (X0 : G) : sK0 ≠ (sK2 ◇ ((X0 ◇ sK2) ◇ (sK2 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq28 eq9


@[equational_result]
theorem Equation964_implies_Equation4666 (G : Type*) [Magma G] (h : Equation964 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq26 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq63 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X4 ◇ X0) ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X2)))) := superpose eq12 eq26 -- superposition 26,12, 12 into 26, unify on (0).2 in 12 and (0).1.2.2 in 26
  have eq79 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X4 ◇ X0) ◇ X2) := superpose eq9 eq63 -- forward demodulation 63,9
  have eq181 (X0 : G) : ((sK0 ◇ sK1) ◇ sK1) ≠ ((X0 ◇ sK1) ◇ sK1) := superpose eq79 eq10 -- superposition 10,79, 79 into 10, unify on (0).2 in 79 and (0).2 in 10
  subsumption eq181 eq79


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
theorem Equation1560_implies_Equation4070 (G : Type*) [Magma G] (h : Equation1560 G) : Equation4070 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation1560_implies_Equation632 (G : Type*) [Magma G] (h : Equation1560 G) : Equation632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
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
  have eq194 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq16 eq166 -- superposition 166,16, 16 into 166, unify on (0).2 in 16 and (0).1.2.2 in 166
  have eq203 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq194 eq10 -- backward demodulation 10,194
  subsumption eq203 eq80


@[equational_result]
theorem Equation1560_implies_Equation619 (G : Type*) [Magma G] (h : Equation1560 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq73 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2.2 in 11
  have eq102 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq73 eq11 -- superposition 11,73, 73 into 11, unify on (0).2 in 73 and (0).1.2 in 11
  have eq223 : sK0 ≠ sK0 := superpose eq102 eq14 -- superposition 14,102, 102 into 14, unify on (0).2 in 102 and (0).2 in 14
  subsumption eq223 rfl


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
theorem Equation1560_implies_Equation4606 (G : Type*) [Magma G] (h : Equation1560 G) : Equation4606 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.2 in 11
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq88 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq96 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq88 -- forward demodulation 88,9
  have eq97 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq96 -- forward demodulation 96,13
  have eq137 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq81 eq12 -- superposition 12,81, 81 into 12, unify on (0).2 in 81 and (0).1.2 in 12
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq137 -- forward demodulation 137,9
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq97 eq146 -- forward demodulation 146,97
  have eq156 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq147 eq22 -- backward demodulation 22,147
  have eq172 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X3 := superpose eq156 eq11 -- backward demodulation 11,156
  have eq200 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2)) := superpose eq172 eq9 -- superposition 9,172, 172 into 9, unify on (0).2 in 172 and (0).1.2.2 in 9
  have eq218 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = ((X3 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq147 eq200 -- forward demodulation 200,147
  have eq1036 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq16 eq218 -- superposition 218,16, 16 into 218, unify on (0).2 in 16 and (0).1.2 in 218
  have eq1335 (X0 : G) : ((sK0 ◇ sK0) ◇ sK1) ≠ ((X0 ◇ sK0) ◇ sK1) := superpose eq1036 eq10 -- superposition 10,1036, 1036 into 10, unify on (0).2 in 1036 and (0).2 in 10
  subsumption eq1335 eq1036


@[equational_result]
theorem Equation1560_implies_Equation4666 (G : Type*) [Magma G] (h : Equation1560 G) : Equation4666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq13


@[equational_result]
theorem Equation1560_implies_Equation642 (G : Type*) [Magma G] (h : Equation1560 G) : Equation642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
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
  have eq194 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq16 eq166 -- superposition 166,16, 16 into 166, unify on (0).2 in 16 and (0).1.2.2 in 166
  have eq203 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq194 eq10 -- backward demodulation 10,194
  subsumption eq203 eq80


@[equational_result]
theorem Equation1560_implies_Equation817 (G : Type*) [Magma G] (h : Equation1560 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.2.2 in 8
  have eq30 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1.1.2 in 15
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.2.2 in 10
  have eq43 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) := superpose eq15 eq30 -- forward demodulation 30,15
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq37 eq10 -- superposition 10,37, 37 into 10, unify on (0).2 in 37 and (0).1.2 in 10
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq37 eq8 -- superposition 8,37, 37 into 8, unify on (0).2 in 37 and (0).1.2.2 in 8
  have eq95 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq8 eq87 -- forward demodulation 87,8
  have eq96 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq95 -- forward demodulation 95,12
  have eq100 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ (X2 ◇ X2)) := superpose eq96 eq43 -- backward demodulation 43,96
  have eq101 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq100 eq9 -- backward demodulation 9,100
  subsumption eq101 eq80


@[equational_result]
theorem Equation1560_implies_Equation3862 (G : Type*) [Magma G] (h : Equation1560 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq12 eq8 -- superposition 8,12, 12 into 8, unify on (0).2 in 12 and (0).1.2.2 in 8
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).1.2.2 in 10
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq37 eq8 -- superposition 8,37, 37 into 8, unify on (0).2 in 37 and (0).1.2.2 in 8
  have eq95 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq8 eq87 -- forward demodulation 87,8
  have eq96 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq95 -- forward demodulation 95,12
  have eq221 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq96 eq9 -- superposition 9,96, 96 into 9, unify on (0).2 in 96 and (0).2 in 9
  subsumption eq221 rfl


@[equational_result]
theorem Equation1560_implies_Equation3887 (G : Type*) [Magma G] (h : Equation1560 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq88 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq96 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq88 -- forward demodulation 88,9
  have eq97 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq96 -- forward demodulation 96,13
  have eq137 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq81 eq12 -- superposition 12,81, 81 into 12, unify on (0).2 in 81 and (0).1.2 in 12
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq137 -- forward demodulation 137,9
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq97 eq146 -- forward demodulation 146,97
  have eq306 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq147 eq10 -- superposition 10,147, 147 into 10, unify on (0).2 in 147 and (0).2 in 10
  subsumption eq306 rfl


@[equational_result]
theorem Equation1560_implies_Equation3877 (G : Type*) [Magma G] (h : Equation1560 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq87 -- forward demodulation 87,9
  have eq95 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq80 eq12 -- superposition 12,80, 80 into 12, unify on (0).2 in 80 and (0).1.2 in 12
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq95 eq143 -- forward demodulation 143,95
  have eq306 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq144 eq10 -- superposition 10,144, 144 into 10, unify on (0).2 in 144 and (0).2 in 10
  subsumption eq306 rfl


@[equational_result]
theorem Equation1560_implies_Equation832 (G : Type*) [Magma G] (h : Equation1560 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq31 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).1.1.2 in 16
  have eq42 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq44 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) := superpose eq16 eq31 -- forward demodulation 31,16
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq42 eq11 -- superposition 11,42, 42 into 11, unify on (0).2 in 42 and (0).1.2 in 11
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq42 eq9 -- superposition 9,42, 42 into 9, unify on (0).2 in 42 and (0).1.2.2 in 9
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq87 -- forward demodulation 87,9
  have eq95 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq99 (X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X3 ◇ X2) ◇ (X2 ◇ X2)) := superpose eq95 eq44 -- backward demodulation 44,95
  have eq100 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq99 eq10 -- backward demodulation 10,99
  subsumption eq100 eq80


@[equational_result]
theorem Equation1560_implies_Equation3867 (G : Type*) [Magma G] (h : Equation1560 G) : Equation3867 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2.2 in 11
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq38 eq11 -- superposition 11,38, 38 into 11, unify on (0).2 in 38 and (0).1.2 in 11
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq9 -- superposition 9,38, 38 into 9, unify on (0).2 in 38 and (0).1.2.2 in 9
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq87 -- forward demodulation 87,9
  have eq95 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq94 -- forward demodulation 94,13
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq80 eq12 -- superposition 12,80, 80 into 12, unify on (0).2 in 80 and (0).1.2 in 12
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq136 -- forward demodulation 136,9
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq95 eq143 -- forward demodulation 143,95
  have eq306 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq144 eq10 -- superposition 10,144, 144 into 10, unify on (0).2 in 144 and (0).2 in 10
  subsumption eq306 rfl


@[equational_result]
theorem Equation960_implies_Equation1560 (G : Type*) [Magma G] (h : Equation960 G) : Equation1560 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq1195 : sK0 ≠ sK0 := superpose eq890 eq10 -- superposition 10,890, 890 into 10, unify on (0).2 in 890 and (0).2 in 10
  subsumption eq1195 rfl


@[equational_result]
theorem Equation960_implies_Equation3897 (G : Type*) [Magma G] (h : Equation960 G) : Equation3897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq123 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2.2 in 17
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq415 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ X0) ◇ X0) := superpose eq120 eq199 -- superposition 199,120, 120 into 199, unify on (0).2 in 120 and (0).2.1 in 199
  have eq447 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq866 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X0) = (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq400 eq400 -- superposition 400,400, 400 into 400, unify on (0).2 in 400 and (0).1.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq899 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq447 eq866 -- forward demodulation 866,447
  have eq1168 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq120 eq890 -- superposition 890,120, 120 into 890, unify on (0).2 in 120 and (0).1.2.2 in 890
  have eq1235 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq123 eq1168 -- forward demodulation 1168,123
  have eq1774 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ (sK2 ◇ sK0)) ◇ sK0) := superpose eq1235 eq10 -- superposition 10,1235, 1235 into 10, unify on (0).2 in 1235 and (0).2 in 10
  subsumption eq1774 eq899


@[equational_result]
theorem Equation960_implies_Equation4080 (G : Type*) [Magma G] (h : Equation960 G) : Equation4080 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq116 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq170 (X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X2) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).2.2 in 16
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.2 in 16
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq415 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq116 eq199 -- superposition 199,116, 116 into 199, unify on (0).2 in 116 and (0).2.1 in 199
  have eq448 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq449 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq448 eq10 -- backward demodulation 10,448
  subsumption eq449 eq170


@[equational_result]
theorem Equation960_implies_Equation4100 (G : Type*) [Magma G] (h : Equation960 G) : Equation4100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq17 eq17 -- superposition 17,17, 17 into 17, unify on (0).2 in 17 and (0).2.2 in 17
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq415 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ X0) ◇ X0) := superpose eq120 eq199 -- superposition 199,120, 120 into 199, unify on (0).2 in 120 and (0).2.1 in 199
  have eq448 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq616 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq448 eq10 -- superposition 10,448, 448 into 10, unify on (0).2 in 448 and (0).2 in 10
  subsumption eq616 rfl


@[equational_result]
theorem Equation960_implies_Equation47 (G : Type*) [Magma G] (h : Equation960 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq45 : sK0 ≠ sK0 := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2 in 9
  subsumption eq45 rfl


@[equational_result]
theorem Equation960_implies_Equation1478 (G : Type*) [Magma G] (h : Equation960 G) : Equation1478 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq35 (X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ (X3 ◇ X3)) ◇ X3) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1 in 12
  have eq121 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq35 -- superposition 35,18, 18 into 35, unify on (0).2 in 18 and (0).1 in 35
  have eq298 : sK0 ≠ sK0 := superpose eq121 eq10 -- superposition 10,121, 121 into 10, unify on (0).2 in 121 and (0).2 in 10
  subsumption eq298 rfl


@[equational_result]
theorem Equation960_implies_Equation1444 (G : Type*) [Magma G] (h : Equation960 G) : Equation1444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq400 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq710 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq858 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq400 -- superposition 400,9, 9 into 400, unify on (0).2 in 9 and (0).1.2.2 in 400
  have eq889 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq710 eq858 -- forward demodulation 858,710
  have eq890 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq889 eq93 -- backward demodulation 93,889
  have eq1195 : sK0 ≠ sK0 := superpose eq890 eq10 -- superposition 10,890, 890 into 10, unify on (0).2 in 890 and (0).2 in 10
  subsumption eq1195 rfl


@[equational_result]
theorem Equation960_implies_Equation364 (G : Type*) [Magma G] (h : Equation960 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1 in 11
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq31 -- forward demodulation 31,12
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).1.2.2 in 18
  have eq116 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq16 eq16 -- superposition 16,16, 16 into 16, unify on (0).2 in 16 and (0).2.2 in 16
  have eq199 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq172 eq41 -- backward demodulation 41,172
  have eq415 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq116 eq199 -- superposition 199,116, 116 into 199, unify on (0).2 in 116 and (0).2.1 in 199
  have eq448 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq100 eq415 -- forward demodulation 415,100
  have eq632 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq448 eq10 -- superposition 10,448, 448 into 10, unify on (0).2 in 448 and (0).2 in 10
  subsumption eq632 rfl


@[equational_result]
theorem Equation960_implies_Equation614 (G : Type*) [Magma G] (h : Equation960 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.1 in 8
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.2 in 8
  have eq17 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).1.1.1 in 10
  have eq115 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq17 eq8 -- superposition 8,17, 17 into 8, unify on (0).2 in 17 and (0).1.2.2 in 8
  have eq137 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq115 eq9 -- backward demodulation 9,115
  subsumption eq137 eq14


@[equational_result]
theorem Equation960_implies_Equation4689 (G : Type*) [Magma G] (h : Equation960 G) : Equation4689 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq18 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X4 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1.1 in 11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).1.2.2 in 11
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X2 := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).1.1.2 in 18
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq18 eq9 -- superposition 9,18, 18 into 9, unify on (0).2 in 18 and (0).1.2.2 in 9
  have eq123 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq13 -- superposition 13,18, 18 into 13, unify on (0).2 in 18 and (0).1 in 13
  have eq403 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X0 := superpose eq120 eq15 -- superposition 15,120, 120 into 15, unify on (0).2 in 120 and (0).1.2 in 15
  have eq711 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq17 eq26 -- superposition 26,17, 17 into 26, unify on (0).2 in 17 and (0).2.2 in 26
  have eq859 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) := superpose eq9 eq403 -- superposition 403,9, 9 into 403, unify on (0).2 in 9 and (0).1.2.2 in 403
  have eq890 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X3 ◇ (X1 ◇ X3)) := superpose eq711 eq859 -- forward demodulation 859,711
  have eq891 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq890 eq93 -- backward demodulation 93,890
  have eq1169 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq120 eq891 -- superposition 891,120, 120 into 891, unify on (0).2 in 120 and (0).1.2.2 in 891
  have eq1236 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X3 ◇ X0) ◇ X2) := superpose eq123 eq1169 -- forward demodulation 1169,123
  have eq1775 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((X0 ◇ sK1) ◇ sK2) := superpose eq1236 eq10 -- superposition 10,1236, 1236 into 10, unify on (0).2 in 1236 and (0).2 in 10
  subsumption eq1775 eq1236


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
theorem Equation930_implies_Equation782 (G : Type*) [Magma G] (h : Equation930 G) : Equation782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq22 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq32 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := superpose eq16 eq22 -- superposition 22,16, 16 into 22, unify on (0).2 in 16 and (0).2 in 22
  subsumption eq32 eq23


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
theorem Equation791_implies_Equation943 (G : Type*) [Magma G] (h : Equation791 G) : Equation943 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = (X4 ◇ (X5 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq14 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq65 (X0 X1 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((X1 ◇ sK0) ◇ sK0))) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.2 in 10
  subsumption eq65 eq9


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
theorem Equation1603_implies_Equation1004 (G : Type*) [Magma G] (h : Equation1603 G) : Equation1004 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X2) = ((X3 ◇ X4) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq17 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq22 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq17 eq14 -- backward demodulation 14,17
  subsumption eq22 eq11


@[equational_result]
theorem Equation757_implies_Equation1510 (G : Type*) [Magma G] (h : Equation757 G) : Equation1510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X1 X2 X3 : G) : (X3 ◇ X1) = (X2 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq88 (X0 : G) : sK0 ≠ ((X0 ◇ sK0) ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq88 eq21


@[equational_result]
theorem Equation78_implies_Equation757 (G : Type*) [Magma G] (h : Equation78 G) : Equation757 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq22 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  subsumption eq22 eq13


@[equational_result]
theorem Equation78_implies_Equation3972 (G : Type*) [Magma G] (h : Equation78 G) : Equation3972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq12


@[equational_result]
theorem Equation719_implies_Equation78 (G : Type*) [Magma G] (h : Equation719 G) : Equation78 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


@[equational_result]
theorem Equation774_implies_Equation1581 (G : Type*) [Magma G] (h : Equation774 G) : Equation1581 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = (X3 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = (X3 ◇ X2) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq33 -- forward demodulation 33,9
  have eq36 (X1 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq18 -- forward demodulation 18,9
  have eq60 (X0 : G) : sK0 ≠ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := superpose eq34 eq10 -- superposition 10,34, 34 into 10, unify on (0).2 in 34 and (0).2 in 10
  subsumption eq60 eq36


@[equational_result]
theorem Equation897_implies_Equation906 (G : Type*) [Magma G] (h : Equation897 G) : Equation906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq24 (X0 : G) : sK0 ≠ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq23


@[equational_result]
theorem Equation897_implies_Equation977 (G : Type*) [Magma G] (h : Equation897 G) : Equation977 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2.2 in 10
  subsumption eq25 eq24


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
theorem Equation977_implies_Equation94 (G : Type*) [Magma G] (h : Equation977 G) : Equation94 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation977_implies_Equation786 (G : Type*) [Magma G] (h : Equation977 G) : Equation786 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation748_implies_Equation3918 (G : Type*) [Magma G] (h : Equation748 G) : Equation3918 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X3 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq32 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq9 eq16 -- forward demodulation 16,9
  have eq81 (X0 : G) : (X0 ◇ sK1) ≠ ((sK0 ◇ (X0 ◇ sK1)) ◇ sK1) := superpose eq32 eq10 -- superposition 10,32, 32 into 10, unify on (0).2 in 32 and (0).1 in 10
  subsumption eq81 eq32


@[equational_result]
theorem Equation748_implies_Equation782 (G : Type*) [Magma G] (h : Equation748 G) : Equation782 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X3 ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq32 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK0 ◇ X0) ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq32 eq9


@[equational_result]
theorem Equation698_implies_Equation1535 (G : Type*) [Magma G] (h : Equation698 G) : Equation1535 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X4 X5 : G) : (X4 ◇ (X5 ◇ (X1 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq73 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq17 eq11 -- superposition 11,17, 17 into 11, unify on (0).2 in 17 and (0).1.2 in 11
  have eq78 (X0 : G) : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2.2 in 10
  subsumption eq78 eq73


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
theorem Equation922_implies_Equation669 (G : Type*) [Magma G] (h : Equation922 G) : Equation669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq25 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq25 eq23


@[equational_result]
theorem Equation922_implies_Equation955 (G : Type*) [Magma G] (h : Equation922 G) : Equation955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq22


@[equational_result]
theorem Equation951_implies_Equation972 (G : Type*) [Magma G] (h : Equation951 G) : Equation972 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq23 eq22


@[equational_result]
theorem Equation972_implies_Equation3925 (G : Type*) [Magma G] (h : Equation972 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X1 X3 X4 : G) : (X3 ◇ X4) = (X1 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq13


@[equational_result]
theorem Equation972_implies_Equation901 (G : Type*) [Magma G] (h : Equation972 G) : Equation901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X3 X4 : G) : (X3 ◇ X4) = (X1 ◇ X4) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X1 X2 X3 X4 : G) : (X1 ◇ (X4 ◇ (X2 ◇ X3))) = X3 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq26 (X0 : G) : sK0 ≠ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq26 eq24


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
theorem Equation1535_implies_Equation616 (G : Type*) [Magma G] (h : Equation1535 G) : Equation616 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq21 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq16 eq10 -- backward demodulation 10,16
  subsumption eq21 eq11


@[equational_result]
theorem Equation694_implies_Equation879 (G : Type*) [Magma G] (h : Equation694 G) : Equation879 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq39 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq11 -- superposition 11,13, 13 into 11, unify on (0).2 in 13 and (0).1.2 in 11
  have eq42 (X0 : G) : sK0 ≠ (sK1 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.2 in 10
  subsumption eq42 eq39


@[equational_result]
theorem Equation694_implies_Equation672 (G : Type*) [Magma G] (h : Equation694 G) : Equation672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq21 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation761_implies_Equation694 (G : Type*) [Magma G] (h : Equation761 G) : Equation694 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq108 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ sK0))) := superpose eq15 eq10 -- superposition 10,15, 15 into 10, unify on (0).2 in 15 and (0).2.2 in 10
  subsumption eq108 eq22


@[equational_result]
theorem Equation761_implies_Equation3901 (G : Type*) [Magma G] (h : Equation761 G) : Equation3901 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq28 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq28 eq12


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
theorem Equation1613_implies_Equation4192 (G : Type*) [Magma G] (h : Equation1613 G) : Equation4192 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((X4 ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq27 (X0 X1 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ X1) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1 in 10
  subsumption eq27 eq13


@[equational_result]
theorem Equation889_implies_Equation1613 (G : Type*) [Magma G] (h : Equation889 G) : Equation1613 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation889_implies_Equation698 (G : Type*) [Magma G] (h : Equation889 G) : Equation698 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation926_implies_Equation1564 (G : Type*) [Magma G] (h : Equation926 G) : Equation1564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X3))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2 in 11
  have eq19 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq19 eq11


@[equational_result]
theorem Equation893_implies_Equation955 (G : Type*) [Magma G] (h : Equation893 G) : Equation955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq37 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1 in 16
  have eq53 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  subsumption eq53 eq37


@[equational_result]
theorem Equation786_implies_Equation1552 (G : Type*) [Magma G] (h : Equation786 G) : Equation1552 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X3 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation90_implies_Equation1498 (G : Type*) [Magma G] (h : Equation90 G) : Equation1498 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.2.2 in 9
  have eq22 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq22 eq19


@[equational_result]
theorem Equation752_implies_Equation1539 (G : Type*) [Magma G] (h : Equation752 G) : Equation1539 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (X2 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq20 rfl


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
theorem Equation666_implies_Equation1598 (G : Type*) [Magma G] (h : Equation666 G) : Equation1598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ X0) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.2 in 13
  have eq75 (X0 : G) : sK0 ≠ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  have eq103 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1.2.1 in 45
  have eq147 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq45 eq103 -- forward demodulation 103,45
  have eq148 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq147 -- forward demodulation 147,9
  have eq160 (X0 X1 : G) : sK0 ≠ (X1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq42 eq75 -- superposition 75,42, 42 into 75, unify on (0).2 in 42 and (0).2.2.2 in 75
  subsumption eq160 eq148


@[equational_result]
theorem Equation666_implies_Equation3997 (G : Type*) [Magma G] (h : Equation666 G) : Equation3997 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ X0) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq23 eq23 -- superposition 23,23, 23 into 23, unify on (0).2 in 23 and (0).1 in 23
  have eq75 (X0 : G) : (sK0 ◇ sK1) ≠ (X0 ◇ sK1) := superpose eq42 eq10 -- superposition 10,42, 42 into 10, unify on (0).2 in 42 and (0).2 in 10
  subsumption eq75 eq42


@[equational_result]
theorem Equation666_implies_Equation774 (G : Type*) [Magma G] (h : Equation666 G) : Equation774 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.1 in 13
  have eq22 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ X0) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq23 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X1 ◇ X0) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq23 eq13 -- superposition 13,23, 23 into 13, unify on (0).2 in 23 and (0).2.2 in 13
  have eq54 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose eq45 eq10 -- backward demodulation 10,45
  subsumption eq54 eq9


@[equational_result]
theorem Equation1564_implies_Equation666 (G : Type*) [Magma G] (h : Equation1564 G) : Equation666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X2 X4 X5 : G) : (X2 ◇ (X4 ◇ (X5 ◇ X4))) = X4 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq19 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq19 rfl


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
theorem Equation1521_implies_Equation4200 (G : Type*) [Magma G] (h : Equation1521 G) : Equation4200 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq81 (X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.1 in 14
  have eq115 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK2) ◇ sK1) := superpose eq81 eq10 -- backward demodulation 10,81
  have eq121 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK2) ◇ sK1) := superpose eq12 eq115 -- forward demodulation 115,12
  have eq129 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq81 eq81 -- superposition 81,81, 81 into 81, unify on (0).2 in 81 and (0).1 in 81
  have eq151 (X0 : G) : (sK0 ◇ sK1) ≠ ((X0 ◇ sK2) ◇ sK1) := superpose eq81 eq121 -- superposition 121,81, 81 into 121, unify on (0).2 in 81 and (0).2.1 in 121
  subsumption eq151 eq129


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
theorem Equation994_implies_Equation1573 (G : Type*) [Magma G] (h : Equation994 G) : Equation1573 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X5 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq11


@[equational_result]
theorem Equation994_implies_Equation1009 (G : Type*) [Magma G] (h : Equation994 G) : Equation1009 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq14 eq9


@[equational_result]
theorem Equation994_implies_Equation3890 (G : Type*) [Magma G] (h : Equation994 G) : Equation3890 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq13 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq22 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq22 rfl


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
theorem Equation1556_implies_Equation3935 (G : Type*) [Magma G] (h : Equation1556 G) : Equation3935 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq24 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ X0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq24 eq13


@[equational_result]
theorem Equation672_implies_Equation4304 (G : Type*) [Magma G] (h : Equation672 G) : Equation4304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq61 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2 in 11
  have eq65 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK2 ◇ (X0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2 in 10
  have eq126 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X5 ◇ X3)) := superpose eq61 eq61 -- superposition 61,61, 61 into 61, unify on (0).2 in 61 and (0).1.2.2 in 61
  have eq229 (X0 : G) : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ ((sK1 ◇ X0) ◇ sK1)) := superpose eq12 eq65 -- superposition 65,12, 12 into 65, unify on (0).2 in 12 and (0).2 in 65
  subsumption eq229 eq126


@[equational_result]
theorem Equation672_implies_Equation686 (G : Type*) [Magma G] (h : Equation672 G) : Equation686 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation672_implies_Equation801 (G : Type*) [Magma G] (h : Equation672 G) : Equation801 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ ((sK3 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq61 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq16 eq11 -- superposition 11,16, 16 into 11, unify on (0).2 in 16 and (0).1.2 in 11
  have eq62 (X0 : G) : sK0 ≠ (sK1 ◇ (sK2 ◇ (X0 ◇ sK0))) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.2.2 in 10
  subsumption eq62 eq61


@[equational_result]
theorem Equation1004_implies_Equation1556 (G : Type*) [Magma G] (h : Equation1004 G) : Equation1556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X4 ◇ (X3 ◇ (X0 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.1 in 9
  have eq13 (X0 X3 X4 : G) : (X0 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq23 (X0 : G) : sK0 ≠ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq23 eq11


@[equational_result]
theorem Equation1004_implies_Equation4175 (G : Type*) [Magma G] (h : Equation1004 G) : Equation4175 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X3 X4 : G) : (X0 ◇ X3) = (X4 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 (X0 : G) : (sK0 ◇ sK1) ≠ (((X0 ◇ sK2) ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2.1.1 in 10
  subsumption eq20 eq13


@[equational_result]
theorem Equation782_implies_Equation735 (G : Type*) [Magma G] (h : Equation782 G) : Equation735 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK3) ◇ sK0))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq35 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ sK0))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2 in 10
  subsumption eq35 eq9


@[equational_result]
theorem Equation955_implies_Equation1004 (G : Type*) [Magma G] (h : Equation955 G) : Equation1004 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq13 (X1 X2 X4 : G) : (X1 ◇ X2) = (X4 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq26 (X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2 in 9
  have eq27 (X0 : G) : sK0 ≠ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK0))) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq27 eq26


@[equational_result]
theorem Equation735_implies_Equation955 (G : Type*) [Magma G] (h : Equation735 G) : Equation955 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK3 ◇ sK0))) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : (X4 ◇ (X4 ◇ (X3 ◇ X5))) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2 in 11
  have eq54 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).1 in 17
  have eq72 (X0 : G) : sK0 ≠ (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  subsumption eq72 eq54


