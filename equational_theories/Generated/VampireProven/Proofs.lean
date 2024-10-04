import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation262_implies_Equation4676 (G : Type*) [Magma G] (h : Equation262 G) : Equation4676 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := (h ..).symm
  have eq10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ sK4) := nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq12 eq9
  have eq22 (X0 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK3) ◇ X0) := superpose eq12 eq10
  have eq54 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X4) ◇ X5) := superpose eq20 eq20
  have eq76 (X0 X1 : G) : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ X0) ◇ X1) := superpose eq12 eq22
  subsumption eq76 eq54


@[equational_result]
theorem Equation1350_implies_Equation654 (G : Type*) [Magma G] (h : Equation1350 G) : Equation654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := (h ..).symm
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1))) := nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X1 := superpose eq9 eq9
  have eq15 (X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X1 ◇ X2) ◇ X2)) = X4 := superpose eq12 eq12
  have eq19 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq12 eq12
  have eq24 : sK0 ≠ (sK0 ◇ sK1) := superpose eq19 eq10
  have eq27 (X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X1 := superpose eq12 eq19
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq27 eq27
  have eq60 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq12 eq27
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq9 eq27
  have eq80 (X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ (X1 ◇ X2)) = X4 := superpose eq59 eq15
  have eq92 (X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) = X4 := superpose eq59 eq80
  have eq93 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X2)) = X4 := superpose eq60 eq92
  have eq101 (X1 X2 X4 : G) : (X2 ◇ X1) = X4 := superpose eq60 eq93
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq24
  subsumption eq104 eq61


@[equational_result]
theorem Equation484_implies_Equation312 (G : Type*) [Magma G] (h : Equation484 G) : Equation312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := (h ..).symm
  have eq10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq9 eq9
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq9 eq13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq9
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq14 eq11
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq17 eq18
  have eq24 : sK0 ≠ (sK0 ◇ sK0) := superpose eq17 eq10
  have eq29 (X1 X2 : G) : X1 = X2 := superpose eq19 eq20
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq24
  subsumption eq39 eq29


@[equational_result]
theorem Equation1554_implies_Equation579 (G : Type*) [Magma G] (h : Equation1554 G) : Equation579 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := (h ..).symm
  have eq10 : sK0 ≠ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) = X3 := superpose eq9 eq9
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq13
  have eq39 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq9
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq20 eq39
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X1 ◇ X2)) := superpose eq42 eq24
  have eq45 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq19 eq44
  have eq46 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq45 eq9
  have eq60 : sK0 ≠ (sK1 ◇ sK2) := superpose eq45 eq10
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq46
  have eq75 (X0 X1 : G) : X0 = X1 := superpose eq61 eq45
  have eq77 : sK0 ≠ sK1 := superpose eq45 eq60
  subsumption eq77 eq75


@[equational_result]
theorem Equation683_implies_Equation1223 (G : Type*) [Magma G] (h : Equation683 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := (h ..).symm
  have eq9 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X3 := superpose eq8 eq8
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq8 eq10
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq10 eq10
  have eq19 : sK0 ≠ (sK0 ◇ sK0) := superpose eq14 eq9
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq15 eq14
  have eq23 (X1 X3 : G) : X1 = X3 := superpose eq10 eq20
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq19
  subsumption eq29 eq23


@[equational_result]
theorem Equation945_implies_Equation436 (G : Type*) [Magma G] (h : Equation945 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := (h ..).symm
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := nh
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X1 := superpose eq13 eq9
  have eq24 (X0 : G) : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ sK0)))) := superpose eq13 eq10
  have eq37 (X0 : G) : sK0 ≠ (sK0 ◇ X0) := superpose eq23 eq24
  have eq42 (X1 : G) : sK0 ≠ X1 := superpose eq9 eq37
  subsumption eq42 rfl
