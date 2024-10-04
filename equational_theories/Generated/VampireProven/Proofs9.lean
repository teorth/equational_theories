import equational_theories.Superposition
import equational_theories.AllEquations
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation650_implies_Equation362 (G : Type*) [Magma G] (h : Equation650 G) : Equation362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
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
  have eq4293 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ (X2 ◇ X3))) = X3 := superpose eq1519 eq3695 -- superposition 3695,1519, 1519 into 3695, unify on (0).2 in 1519 and (0).1.2.1 in 3695
  have eq4617 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq3860 eq3860 -- superposition 3860,3860, 3860 into 3860, unify on (0).2 in 3860 and (0).2.2.2 in 3860
  have eq4720 (X0 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ (X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3))) := superpose eq3837 eq4617 -- forward demodulation 4617,3837
  have eq4725 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2))) := superpose eq4720 eq105 -- backward demodulation 105,4720
  have eq4738 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq4725 eq1173 -- backward demodulation 1173,4725
  have eq4741 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq4738 eq3450 -- backward demodulation 3450,4738
  have eq4831 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X2 := superpose eq1519 eq4741 -- superposition 4741,1519, 1519 into 4741, unify on (0).2 in 1519 and (0).1.2 in 4741
  have eq4859 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) ◇ X5) := superpose eq4831 eq1135 -- backward demodulation 1135,4831
  have eq4860 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ ((X6 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4831 eq1140 -- backward demodulation 1140,4831
  have eq4865 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ X0) := superpose eq4831 eq1519 -- backward demodulation 1519,4831
  have eq4897 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X3 := superpose eq4865 eq4293 -- backward demodulation 4293,4865
  have eq4928 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq4897 eq3024 -- backward demodulation 3024,4897
  have eq5219 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4928 eq4860 -- backward demodulation 4860,4928
  have eq5998 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ (X5 ◇ (X6 ◇ X5)))) := superpose eq4928 eq5219 -- forward demodulation 5219,4928
  have eq5999 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4) := superpose eq4928 eq5998 -- forward demodulation 5998,4928
  have eq6004 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) = ((X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5) := superpose eq5999 eq4859 -- backward demodulation 4859,5999
  have eq6021 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq4928 eq6004 -- forward demodulation 6004,4928
  have eq6493 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq6021 eq10 -- backward demodulation 10,6021
  have eq6494 : sK0 ≠ (sK0 ◇ sK1) := superpose eq6021 eq6493 -- forward demodulation 6493,6021
  subsumption eq6494 eq6021


@[equational_result]
theorem Equation650_implies_Equation646 (G : Type*) [Magma G] (h : Equation650 G) : Equation646 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := mod_symm nh
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
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1579 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1694 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2684 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1694 eq12 -- superposition 12,1694, 1694 into 12, unify on (0).2 in 1694 and (0).1.2.1.2 in 12
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3028 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3181 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3021 eq372 -- superposition 372,3021, 3021 into 372, unify on (0).2 in 3021 and (0).1.2.1.1 in 372
  have eq3227 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3021 eq30 -- superposition 30,3021, 3021 into 30, unify on (0).2 in 3021 and (0).1.2.1 in 30
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3028 -- backward demodulation 3028,3161
  have eq3253 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3018 eq3227 -- forward demodulation 3227,3018
  have eq3256 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3253 eq2684 -- backward demodulation 2684,3253
  have eq3301 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3302 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3311 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3301 eq3181 -- backward demodulation 3181,3301
  have eq3313 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3301 eq3302 -- forward demodulation 3302,3301
  have eq3327 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3313 eq3256 -- backward demodulation 3256,3313
  have eq3414 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq33 -- superposition 33,3313, 3313 into 33, unify on (0).2 in 3313 and (0).1.2.1 in 33
  have eq3458 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3313 eq9 -- superposition 9,3313, 3313 into 9, unify on (0).2 in 3313 and (0).1.2 in 9
  have eq3535 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3313 eq21 -- superposition 21,3313, 3313 into 21, unify on (0).2 in 3313 and (0).1 in 21
  have eq3593 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq3414 -- forward demodulation 3414,3313
  have eq3658 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3313 eq3458 -- superposition 3458,3313, 3313 into 3458, unify on (0).2 in 3313 and (0).1.2 in 3458
  have eq3681 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3458 eq3313 -- superposition 3313,3458, 3458 into 3313, unify on (0).2 in 3458 and (0).1 in 3313
  have eq3859 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3658 eq3311 -- backward demodulation 3311,3658
  have eq4094 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3859 eq11 -- superposition 11,3859, 3859 into 11, unify on (0).2 in 3859 and (0).1.2.1 in 11
  have eq4200 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3859 eq3681 -- superposition 3681,3859, 3859 into 3681, unify on (0).2 in 3859 and (0).1.2.2 in 3681
  have eq4236 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4200 eq4094 -- backward demodulation 4094,4200
  have eq4791 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4236 eq3535 -- backward demodulation 3535,4236
  have eq5350 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4236 eq3327 -- backward demodulation 3327,4236
  have eq5896 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5350 eq4791 -- backward demodulation 4791,5350
  have eq5929 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5896 eq3593 -- backward demodulation 3593,5896
  have eq5948 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := superpose eq5896 eq10 -- backward demodulation 10,5896
  have eq5949 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3658 eq5929 -- forward demodulation 5929,3658
  have eq5957 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5949 eq3681 -- backward demodulation 3681,5949
  subsumption eq5948 eq5957


@[equational_result]
theorem Equation650_implies_Equation3666 (G : Type*) [Magma G] (h : Equation650 G) : Equation3666 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq234 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X2 ◇ X5)) = ((X5 ◇ (X2 ◇ X5)) ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq17 eq21 -- superposition 21,17, 17 into 21, unify on (0).2 in 17 and (0).2.2.2 in 21
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X5 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2))) = X2 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1.2.1 in 12
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq743 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq11 eq239 -- superposition 239,11, 11 into 239, unify on (0).2 in 11 and (0).1.2.1.2 in 239
  have eq1442 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1443 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1445 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1527 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1443 eq1442 -- backward demodulation 1442,1443
  have eq1588 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1704 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1588 -- forward demodulation 1588,11
  have eq1883 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1704 -- superposition 1704,31, 31 into 1704, unify on (0).2 in 31 and (0).2.2.2 in 1704
  have eq1887 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1704 eq9 -- superposition 9,1704, 1704 into 9, unify on (0).2 in 1704 and (0).1.2.2 in 9
  have eq1892 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1704 eq12 -- superposition 12,1704, 1704 into 12, unify on (0).2 in 1704 and (0).1.2.1.2 in 12
  have eq2697 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1887 -- superposition 1887,31, 31 into 1887, unify on (0).2 in 31 and (0).2.2.1.2 in 1887
  have eq2769 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1892 -- superposition 1892,31, 31 into 1892, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1892
  have eq2855 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1445 -- superposition 1445,11, 11 into 1445, unify on (0).2 in 11 and (0).1.2.1.2 in 1445
  have eq2911 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1527 -- superposition 1527,21, 21 into 1527, unify on (0).2 in 21 and (0).1 in 1527
  have eq3024 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2911 eq2769 -- backward demodulation 2769,2911
  have eq3025 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2911 eq2697 -- backward demodulation 2697,2911
  have eq3026 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2911 eq1883 -- backward demodulation 1883,2911
  have eq3028 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3024 -- forward demodulation 3024,11
  have eq3029 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3025 -- forward demodulation 3025,11
  have eq3037 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3026 eq2855 -- backward demodulation 2855,3026
  have eq3169 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3029 eq3028 -- superposition 3028,3029, 3029 into 3028, unify on (0).2 in 3029 and (0).1.2 in 3028
  have eq3259 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3169 eq3037 -- backward demodulation 3037,3169
  have eq3307 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3259 eq55 -- superposition 55,3259, 3259 into 55, unify on (0).2 in 3259 and (0).2.2 in 55
  have eq3308 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3259 eq271 -- superposition 271,3259, 3259 into 271, unify on (0).2 in 3259 and (0).2.2.1 in 271
  have eq3310 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1))) = X1 := superpose eq3259 eq743 -- superposition 743,3259, 3259 into 743, unify on (0).2 in 3259 and (0).1.2.1 in 743
  have eq3320 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3307 eq3308 -- forward demodulation 3308,3307
  have eq3466 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3320 eq9 -- superposition 9,3320, 3320 into 9, unify on (0).2 in 3320 and (0).1.2 in 9
  have eq3676 (X0 X1 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)) := superpose eq3466 eq234 -- superposition 234,3466, 3466 into 234, unify on (0).2 in 3466 and (0).2.2 in 234
  have eq3865 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3676 eq3310 -- backward demodulation 3310,3676
  have eq3992 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq3320 eq3865 -- superposition 3865,3320, 3320 into 3865, unify on (0).2 in 3320 and (0).1.2 in 3865
  have eq4064 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) := superpose eq3992 eq11 -- backward demodulation 11,3992
  have eq5351 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq3992 eq4064 -- forward demodulation 4064,3992
  have eq5365 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := superpose eq5351 eq10 -- backward demodulation 10,5351
  have eq5366 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq5351 eq5365 -- forward demodulation 5365,5351
  have eq5367 : sK0 ≠ (sK0 ◇ sK0) := superpose eq5351 eq5366 -- forward demodulation 5366,5351
  subsumption eq5367 eq5351


@[equational_result]
theorem Equation650_implies_Equation1063 (G : Type*) [Magma G] (h : Equation650 G) : Equation1063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0)) := mod_symm nh
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
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1579 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1694 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2684 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1694 eq12 -- superposition 12,1694, 1694 into 12, unify on (0).2 in 1694 and (0).1.2.1.2 in 12
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3028 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3181 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3021 eq372 -- superposition 372,3021, 3021 into 372, unify on (0).2 in 3021 and (0).1.2.1.1 in 372
  have eq3227 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3021 eq30 -- superposition 30,3021, 3021 into 30, unify on (0).2 in 3021 and (0).1.2.1 in 30
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3028 -- backward demodulation 3028,3161
  have eq3253 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3018 eq3227 -- forward demodulation 3227,3018
  have eq3256 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3253 eq2684 -- backward demodulation 2684,3253
  have eq3301 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3302 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3311 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3301 eq3181 -- backward demodulation 3181,3301
  have eq3313 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3301 eq3302 -- forward demodulation 3302,3301
  have eq3327 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3313 eq3256 -- backward demodulation 3256,3313
  have eq3414 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq33 -- superposition 33,3313, 3313 into 33, unify on (0).2 in 3313 and (0).1.2.1 in 33
  have eq3458 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3313 eq9 -- superposition 9,3313, 3313 into 9, unify on (0).2 in 3313 and (0).1.2 in 9
  have eq3535 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3313 eq21 -- superposition 21,3313, 3313 into 21, unify on (0).2 in 3313 and (0).1 in 21
  have eq3593 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq3414 -- forward demodulation 3414,3313
  have eq3658 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3313 eq3458 -- superposition 3458,3313, 3313 into 3458, unify on (0).2 in 3313 and (0).1.2 in 3458
  have eq3681 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3458 eq3313 -- superposition 3313,3458, 3458 into 3313, unify on (0).2 in 3458 and (0).1 in 3313
  have eq3859 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3658 eq3311 -- backward demodulation 3311,3658
  have eq4076 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3859 eq11 -- superposition 11,3859, 3859 into 11, unify on (0).2 in 3859 and (0).1.2.1 in 11
  have eq4182 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3859 eq3681 -- superposition 3681,3859, 3859 into 3681, unify on (0).2 in 3859 and (0).1.2.2 in 3681
  have eq4218 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4182 eq4076 -- backward demodulation 4076,4182
  have eq4773 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4218 eq3535 -- backward demodulation 3535,4218
  have eq5332 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4218 eq3327 -- backward demodulation 3327,4218
  have eq5878 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5332 eq4773 -- backward demodulation 4773,5332
  have eq5911 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5878 eq3593 -- backward demodulation 3593,5878
  have eq5930 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq5878 eq10 -- backward demodulation 10,5878
  have eq5931 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3658 eq5911 -- forward demodulation 5911,3658
  have eq5939 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5931 eq3681 -- backward demodulation 3681,5931
  subsumption eq5930 eq5939


@[equational_result]
theorem Equation650_implies_Equation53 (G : Type*) [Magma G] (h : Equation650 G) : Equation53 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1695 -- superposition 1695,31, 31 into 1695, unify on (0).2 in 31 and (0).2.2.2 in 1695
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1695 eq9 -- superposition 9,1695, 1695 into 9, unify on (0).2 in 1695 and (0).1.2.2 in 9
  have eq1883 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1695 eq12 -- superposition 12,1695, 1695 into 12, unify on (0).2 in 1695 and (0).1.2.1.2 in 12
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
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3160 eq3027 -- backward demodulation 3027,3160
  have eq3300 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3250 eq55 -- superposition 55,3250, 3250 into 55, unify on (0).2 in 3250 and (0).2.2 in 55
  have eq3301 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3250 eq271 -- superposition 271,3250, 3250 into 271, unify on (0).2 in 3250 and (0).2.2.1 in 271
  have eq3312 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3300 eq3301 -- forward demodulation 3301,3300
  have eq3457 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3312 eq9 -- superposition 9,3312, 3312 into 9, unify on (0).2 in 3312 and (0).1.2 in 9
  have eq3687 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3457 eq3312 -- superposition 3312,3457, 3457 into 3312, unify on (0).2 in 3457 and (0).1 in 3312
  have eq4176 : sK0 ≠ sK0 := superpose eq3687 eq10 -- superposition 10,3687, 3687 into 10, unify on (0).2 in 3687 and (0).2 in 10
  subsumption eq4176 rfl


@[equational_result]
theorem Equation650_implies_Equation3738 (G : Type*) [Magma G] (h : Equation650 G) : Equation3738 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq47 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4)) = ((X4 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4)) ◇ (X5 ◇ ((X6 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X6)) ◇ X5))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2.1.2.1 in 21
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq372 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq12 -- superposition 12,55, 55 into 12, unify on (0).2 in 55 and (0).1.2.1.2 in 12
  have eq1442 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1443 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1445 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1527 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1443 eq1442 -- backward demodulation 1442,1443
  have eq1588 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1704 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1588 -- forward demodulation 1588,11
  have eq1883 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1704 -- superposition 1704,31, 31 into 1704, unify on (0).2 in 31 and (0).2.2.2 in 1704
  have eq1887 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1704 eq9 -- superposition 9,1704, 1704 into 9, unify on (0).2 in 1704 and (0).1.2.2 in 9
  have eq1892 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1704 eq12 -- superposition 12,1704, 1704 into 12, unify on (0).2 in 1704 and (0).1.2.1.2 in 12
  have eq2697 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1887 -- superposition 1887,31, 31 into 1887, unify on (0).2 in 31 and (0).2.2.1.2 in 1887
  have eq2769 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1892 -- superposition 1892,31, 31 into 1892, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1892
  have eq2855 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1445 -- superposition 1445,11, 11 into 1445, unify on (0).2 in 11 and (0).1.2.1.2 in 1445
  have eq2911 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1527 -- superposition 1527,21, 21 into 1527, unify on (0).2 in 21 and (0).1 in 1527
  have eq3024 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2911 eq2769 -- backward demodulation 2769,2911
  have eq3025 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2911 eq2697 -- backward demodulation 2697,2911
  have eq3026 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2911 eq1883 -- backward demodulation 1883,2911
  have eq3028 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3024 -- forward demodulation 3024,11
  have eq3029 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3025 -- forward demodulation 3025,11
  have eq3037 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3026 eq2855 -- backward demodulation 2855,3026
  have eq3169 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3029 eq3028 -- superposition 3028,3029, 3029 into 3028, unify on (0).2 in 3029 and (0).1.2 in 3028
  have eq3189 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3029 eq372 -- superposition 372,3029, 3029 into 372, unify on (0).2 in 3029 and (0).1.2.1.1 in 372
  have eq3259 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3169 eq3037 -- backward demodulation 3037,3169
  have eq3309 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3259 eq55 -- superposition 55,3259, 3259 into 55, unify on (0).2 in 3259 and (0).2.2 in 55
  have eq3310 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3259 eq271 -- superposition 271,3259, 3259 into 271, unify on (0).2 in 3259 and (0).2.2.1 in 271
  have eq3311 (X0 X1 X3 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X3))) = X3 := superpose eq3259 eq372 -- superposition 372,3259, 3259 into 372, unify on (0).2 in 3259 and (0).1.2.1.1 in 372
  have eq3318 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3309 eq3189 -- backward demodulation 3189,3309
  have eq3320 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3309 eq3310 -- forward demodulation 3310,3309
  have eq3384 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X3))) = X3 := superpose eq3309 eq3311 -- forward demodulation 3311,3309
  have eq3466 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3320 eq9 -- superposition 9,3320, 3320 into 9, unify on (0).2 in 3320 and (0).1.2 in 9
  have eq3664 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3320 eq3466 -- superposition 3466,3320, 3320 into 3466, unify on (0).2 in 3320 and (0).1.2 in 3466
  have eq3686 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3466 eq3320 -- superposition 3320,3466, 3466 into 3320, unify on (0).2 in 3466 and (0).1 in 3320
  have eq3863 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3664 eq3318 -- backward demodulation 3318,3664
  have eq4129 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3863 eq11 -- superposition 11,3863, 3863 into 11, unify on (0).2 in 3863 and (0).1.2.1 in 11
  have eq4259 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3863 eq3686 -- superposition 3686,3863, 3863 into 3686, unify on (0).2 in 3863 and (0).1.2.2 in 3686
  have eq4295 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4259 eq4129 -- backward demodulation 4129,4259
  have eq4505 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X2 ◇ X3))) = ((X4 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X5 ◇ ((X6 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X6)) ◇ X5))) := superpose eq4295 eq47 -- backward demodulation 47,4295
  have eq4945 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq4295 eq3384 -- backward demodulation 3384,4295
  have eq5674 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X2 ◇ X3))) = ((X4 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X5 ◇ (X6 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X6)))) := superpose eq4295 eq4505 -- forward demodulation 4505,4295
  have eq5675 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ (X2 ◇ X3))) = ((X4 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X5 ◇ (X6 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) := superpose eq4295 eq5674 -- forward demodulation 5674,4295
  have eq5884 (X0 X1 X2 X4 X5 X6 : G) : (X4 ◇ (X5 ◇ (X6 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) = X4 := superpose eq4945 eq5675 -- backward demodulation 5675,4945
  have eq5915 (X4 X5 X6 : G) : (X4 ◇ (X5 ◇ X6)) = X4 := superpose eq4945 eq5884 -- forward demodulation 5884,4945
  have eq5916 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) := superpose eq5915 eq11 -- backward demodulation 11,5915
  have eq5953 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq5915 eq5916 -- forward demodulation 5916,5915
  have eq5963 : sK0 ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK3)) := superpose eq5953 eq10 -- backward demodulation 10,5953
  have eq5964 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq5953 eq5963 -- forward demodulation 5963,5953
  have eq5965 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5953 eq5964 -- forward demodulation 5964,5953
  subsumption eq5965 eq5953


@[equational_result]
theorem Equation650_implies_Equation3668 (G : Type*) [Magma G] (h : Equation650 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
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
  have eq1428 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1429 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1431 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq38 -- superposition 38,23, 23 into 38, unify on (0).2 in 23 and (0).1.2.1 in 38
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1429 eq1428 -- backward demodulation 1428,1429
  have eq1538 (X0 X1 X2 X4 : G) : (X4 ◇ (((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq23 eq390 -- superposition 390,23, 23 into 390, unify on (0).2 in 23 and (0).1.2.1.1 in 390
  have eq1544 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq1429 eq1538 -- forward demodulation 1538,1429
  have eq1572 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq35 -- superposition 35,13, 13 into 35, unify on (0).2 in 13 and (0).2.2.1.2.1 in 35
  have eq1573 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq34 eq35 -- superposition 35,34, 34 into 35, unify on (0).2 in 34 and (0).2.2.1.2.1 in 35
  have eq1687 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1572 -- forward demodulation 1572,11
  have eq1689 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1573 -- forward demodulation 1573,11
  have eq1692 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq11 eq1544 -- superposition 1544,11, 11 into 1544, unify on (0).2 in 11 and (0).1.2.1.2 in 1544
  have eq1868 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1689 -- superposition 1689,31, 31 into 1689, unify on (0).2 in 31 and (0).2.2.2 in 1689
  have eq1873 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1689 eq9 -- superposition 9,1689, 1689 into 9, unify on (0).2 in 1689 and (0).1.2.2 in 9
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1689 eq12 -- superposition 12,1689, 1689 into 12, unify on (0).2 in 1689 and (0).1.2.1.2 in 12
  have eq2280 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) = ((X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq24 eq30 -- superposition 30,24, 24 into 30, unify on (0).2 in 24 and (0).1.2.1 in 30
  have eq2677 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq1687 eq21 -- superposition 21,1687, 1687 into 21, unify on (0).2 in 1687 and (0).2.2.2 in 21
  have eq2682 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1873 -- superposition 1873,31, 31 into 1873, unify on (0).2 in 31 and (0).2.2.1.2 in 1873
  have eq2754 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1878 -- superposition 1878,31, 31 into 1878, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1878
  have eq2840 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1431 -- superposition 1431,11, 11 into 1431, unify on (0).2 in 11 and (0).1.2.1.2 in 1431
  have eq2896 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3009 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2896 eq2754 -- backward demodulation 2754,2896
  have eq3010 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2896 eq2682 -- backward demodulation 2682,2896
  have eq3011 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2896 eq1868 -- backward demodulation 1868,2896
  have eq3013 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3009 -- forward demodulation 3009,11
  have eq3014 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3010 -- forward demodulation 3010,11
  have eq3018 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq3011 eq1692 -- backward demodulation 1692,3011
  have eq3022 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3011 eq2840 -- backward demodulation 2840,3011
  have eq3154 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3014 eq3013 -- superposition 3013,3014, 3014 into 3013, unify on (0).2 in 3014 and (0).1.2 in 3013
  have eq3177 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3014 eq30 -- superposition 30,3014, 3014 into 30, unify on (0).2 in 3014 and (0).1.2.1 in 30
  have eq3244 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3154 eq3022 -- backward demodulation 3022,3154
  have eq3245 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3011 eq3177 -- forward demodulation 3177,3011
  have eq3247 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := superpose eq3245 eq2677 -- backward demodulation 2677,3245
  have eq3295 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3244 eq55 -- superposition 55,3244, 3244 into 55, unify on (0).2 in 3244 and (0).2.2 in 55
  have eq3296 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3244 eq271 -- superposition 271,3244, 3244 into 271, unify on (0).2 in 3244 and (0).2.2.1 in 271
  have eq3309 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3295 eq3296 -- forward demodulation 3296,3295
  have eq3324 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq3309 eq3247 -- backward demodulation 3247,3309
  have eq3420 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq3324 eq390 -- backward demodulation 390,3324
  have eq3435 (X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq3324 eq743 -- backward demodulation 743,3324
  have eq3533 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq3324 eq2280 -- backward demodulation 2280,3324
  have eq3685 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) = X0 := superpose eq3295 eq3420 -- forward demodulation 3420,3295
  have eq3694 (X0 X1 X2 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ (X6 ◇ (X2 ◇ X6))) := superpose eq3324 eq3533 -- forward demodulation 3533,3324
  have eq3768 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4))) := superpose eq3694 eq34 -- backward demodulation 34,3694
  have eq4288 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ (X2 ◇ X3))) = X3 := superpose eq1519 eq3685 -- superposition 3685,1519, 1519 into 3685, unify on (0).2 in 1519 and (0).1.2.1 in 3685
  have eq4612 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq3768 eq3768 -- superposition 3768,3768, 3768 into 3768, unify on (0).2 in 3768 and (0).2.2.2 in 3768
  have eq4715 (X0 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ (X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3))) := superpose eq3694 eq4612 -- forward demodulation 4612,3694
  have eq4720 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2))) := superpose eq4715 eq105 -- backward demodulation 105,4715
  have eq4734 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq4720 eq1173 -- backward demodulation 1173,4720
  have eq4736 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq4734 eq3435 -- backward demodulation 3435,4734
  have eq4826 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X2 := superpose eq1519 eq4736 -- superposition 4736,1519, 1519 into 4736, unify on (0).2 in 1519 and (0).1.2 in 4736
  have eq4854 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) ◇ X5) := superpose eq4826 eq1135 -- backward demodulation 1135,4826
  have eq4855 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ ((X6 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4826 eq1140 -- backward demodulation 1140,4826
  have eq4860 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ X0) := superpose eq4826 eq1519 -- backward demodulation 1519,4826
  have eq4891 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X3 := superpose eq4860 eq4288 -- backward demodulation 4288,4860
  have eq4922 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq4891 eq3018 -- backward demodulation 3018,4891
  have eq5212 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4922 eq4855 -- backward demodulation 4855,4922
  have eq5991 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ (X5 ◇ (X6 ◇ X5)))) := superpose eq4922 eq5212 -- forward demodulation 5212,4922
  have eq5992 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4) := superpose eq4922 eq5991 -- forward demodulation 5991,4922
  have eq5997 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) = ((X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5) := superpose eq5992 eq4854 -- backward demodulation 4854,5992
  have eq6014 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq4922 eq5997 -- forward demodulation 5997,4922
  have eq6480 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := superpose eq6014 eq10 -- backward demodulation 10,6014
  have eq6481 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq6014 eq6480 -- forward demodulation 6480,6014
  have eq6482 : sK0 ≠ (sK0 ◇ sK1) := superpose eq6014 eq6481 -- forward demodulation 6481,6014
  subsumption eq6482 eq6014


@[equational_result]
theorem Equation650_implies_Equation3664 (G : Type*) [Magma G] (h : Equation650 G) : Equation3664 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq234 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X2 ◇ X5)) = ((X5 ◇ (X2 ◇ X5)) ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq17 eq21 -- superposition 21,17, 17 into 21, unify on (0).2 in 17 and (0).2.2.2 in 21
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X5 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2))) = X2 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1.2.1 in 12
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq743 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq11 eq239 -- superposition 239,11, 11 into 239, unify on (0).2 in 11 and (0).1.2.1.2 in 239
  have eq1442 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1443 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1445 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1527 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1443 eq1442 -- backward demodulation 1442,1443
  have eq1588 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1704 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1588 -- forward demodulation 1588,11
  have eq1883 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1704 -- superposition 1704,31, 31 into 1704, unify on (0).2 in 31 and (0).2.2.2 in 1704
  have eq1887 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1704 eq9 -- superposition 9,1704, 1704 into 9, unify on (0).2 in 1704 and (0).1.2.2 in 9
  have eq1892 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1704 eq12 -- superposition 12,1704, 1704 into 12, unify on (0).2 in 1704 and (0).1.2.1.2 in 12
  have eq2697 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1887 -- superposition 1887,31, 31 into 1887, unify on (0).2 in 31 and (0).2.2.1.2 in 1887
  have eq2769 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1892 -- superposition 1892,31, 31 into 1892, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1892
  have eq2855 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1445 -- superposition 1445,11, 11 into 1445, unify on (0).2 in 11 and (0).1.2.1.2 in 1445
  have eq2911 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1527 -- superposition 1527,21, 21 into 1527, unify on (0).2 in 21 and (0).1 in 1527
  have eq3024 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2911 eq2769 -- backward demodulation 2769,2911
  have eq3025 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2911 eq2697 -- backward demodulation 2697,2911
  have eq3026 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2911 eq1883 -- backward demodulation 1883,2911
  have eq3028 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3024 -- forward demodulation 3024,11
  have eq3029 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3025 -- forward demodulation 3025,11
  have eq3037 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3026 eq2855 -- backward demodulation 2855,3026
  have eq3169 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3029 eq3028 -- superposition 3028,3029, 3029 into 3028, unify on (0).2 in 3029 and (0).1.2 in 3028
  have eq3259 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3169 eq3037 -- backward demodulation 3037,3169
  have eq3307 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3259 eq55 -- superposition 55,3259, 3259 into 55, unify on (0).2 in 3259 and (0).2.2 in 55
  have eq3308 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3259 eq271 -- superposition 271,3259, 3259 into 271, unify on (0).2 in 3259 and (0).2.2.1 in 271
  have eq3310 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1))) = X1 := superpose eq3259 eq743 -- superposition 743,3259, 3259 into 743, unify on (0).2 in 3259 and (0).1.2.1 in 743
  have eq3320 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3307 eq3308 -- forward demodulation 3308,3307
  have eq3466 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3320 eq9 -- superposition 9,3320, 3320 into 9, unify on (0).2 in 3320 and (0).1.2 in 9
  have eq3676 (X0 X1 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)) := superpose eq3466 eq234 -- superposition 234,3466, 3466 into 234, unify on (0).2 in 3466 and (0).2.2 in 234
  have eq3865 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3676 eq3310 -- backward demodulation 3310,3676
  have eq3992 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq3320 eq3865 -- superposition 3865,3320, 3320 into 3865, unify on (0).2 in 3320 and (0).1.2 in 3865
  have eq4064 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) := superpose eq3992 eq11 -- backward demodulation 11,3992
  have eq5351 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq3992 eq4064 -- forward demodulation 4064,3992
  have eq5365 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq5351 eq10 -- backward demodulation 10,5351
  have eq5366 : sK0 ≠ (sK0 ◇ sK0) := superpose eq5351 eq5365 -- forward demodulation 5365,5351
  subsumption eq5366 eq5351


@[equational_result]
theorem Equation650_implies_Equation4476 (G : Type*) [Magma G] (h : Equation650 G) : Equation4476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq234 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X2 ◇ X5)) = ((X5 ◇ (X2 ◇ X5)) ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq17 eq21 -- superposition 21,17, 17 into 21, unify on (0).2 in 17 and (0).2.2.2 in 21
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X5 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2))) = X2 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1.2.1 in 12
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq743 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq11 eq239 -- superposition 239,11, 11 into 239, unify on (0).2 in 11 and (0).1.2.1.2 in 239
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3028 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3028 -- backward demodulation 3028,3161
  have eq3299 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3300 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3302 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1))) = X1 := superpose eq3251 eq743 -- superposition 743,3251, 3251 into 743, unify on (0).2 in 3251 and (0).1.2.1 in 743
  have eq3313 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3299 eq3300 -- forward demodulation 3300,3299
  have eq3458 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3313 eq9 -- superposition 9,3313, 3313 into 9, unify on (0).2 in 3313 and (0).1.2 in 9
  have eq3665 (X0 X1 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)) := superpose eq3458 eq234 -- superposition 234,3458, 3458 into 234, unify on (0).2 in 3458 and (0).2.2 in 234
  have eq3860 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3665 eq3302 -- backward demodulation 3302,3665
  have eq3980 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq3313 eq3860 -- superposition 3860,3313, 3313 into 3860, unify on (0).2 in 3313 and (0).1.2 in 3860
  have eq4031 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) := superpose eq3980 eq11 -- backward demodulation 11,3980
  have eq5316 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq3980 eq4031 -- forward demodulation 4031,3980
  have eq5330 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK1) := superpose eq5316 eq10 -- backward demodulation 10,5316
  have eq5331 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5316 eq5330 -- forward demodulation 5330,5316
  subsumption eq5331 eq5316


@[equational_result]
theorem Equation650_implies_Equation3732 (G : Type*) [Magma G] (h : Equation650 G) : Equation3732 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2 in 9
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.1.2.1.2 in 12
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.2.1 in 11
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.2.1 in 11
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2 in 12
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1 in 12
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq234 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X2 ◇ X5)) = ((X5 ◇ (X2 ◇ X5)) ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq17 eq21 -- superposition 21,17, 17 into 21, unify on (0).2 in 17 and (0).2.2.2 in 21
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X5 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X3)) ◇ X2))) = X2 := superpose eq17 eq12 -- superposition 12,17, 17 into 12, unify on (0).2 in 17 and (0).1.2.1.2.1 in 12
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq743 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq11 eq239 -- superposition 239,11, 11 into 239, unify on (0).2 in 11 and (0).1.2.1.2 in 239
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3029 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3029 -- backward demodulation 3029,3161
  have eq3299 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3300 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3302 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1))) = X1 := superpose eq3251 eq743 -- superposition 743,3251, 3251 into 743, unify on (0).2 in 3251 and (0).1.2.1 in 743
  have eq3313 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3299 eq3300 -- forward demodulation 3300,3299
  have eq3459 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3313 eq9 -- superposition 9,3313, 3313 into 9, unify on (0).2 in 3313 and (0).1.2 in 9
  have eq3671 (X0 X1 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2)) := superpose eq3459 eq234 -- superposition 234,3459, 3459 into 234, unify on (0).2 in 3459 and (0).2.2 in 234
  have eq3861 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3671 eq3302 -- backward demodulation 3302,3671
  have eq3988 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq3313 eq3861 -- superposition 3861,3313, 3313 into 3861, unify on (0).2 in 3313 and (0).1.2 in 3861
  have eq4060 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) := superpose eq3988 eq11 -- backward demodulation 11,3988
  have eq5348 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq3988 eq4060 -- forward demodulation 4060,3988
  have eq5362 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK0) := superpose eq5348 eq10 -- backward demodulation 10,5348
  have eq5363 : sK0 ≠ (sK0 ◇ sK0) := superpose eq5348 eq5362 -- forward demodulation 5362,5348
  subsumption eq5363 eq5348


@[equational_result]
theorem Equation650_implies_Equation4516 (G : Type*) [Magma G] (h : Equation650 G) : Equation4516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
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
  have eq1172 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))) := superpose eq9 eq1097 -- forward demodulation 1097,9
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq38 -- superposition 38,23, 23 into 38, unify on (0).2 in 23 and (0).1.2.1 in 38
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1543 (X0 X1 X2 X4 : G) : (X4 ◇ (((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq23 eq390 -- superposition 390,23, 23 into 390, unify on (0).2 in 23 and (0).1.2.1.1 in 390
  have eq1550 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) = X4 := superpose eq1434 eq1543 -- forward demodulation 1543,1434
  have eq1578 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq35 -- superposition 35,13, 13 into 35, unify on (0).2 in 13 and (0).2.2.1.2.1 in 35
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq34 eq35 -- superposition 35,34, 34 into 35, unify on (0).2 in 34 and (0).2.2.1.2.1 in 35
  have eq1693 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1578 -- forward demodulation 1578,11
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1698 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq11 eq1550 -- superposition 1550,11, 11 into 1550, unify on (0).2 in 11 and (0).1.2.1.2 in 1550
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1695 -- superposition 1695,31, 31 into 1695, unify on (0).2 in 31 and (0).2.2.2 in 1695
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1695 eq9 -- superposition 9,1695, 1695 into 9, unify on (0).2 in 1695 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1695 eq12 -- superposition 12,1695, 1695 into 12, unify on (0).2 in 1695 and (0).1.2.1.2 in 12
  have eq2286 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) = ((X5 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq24 eq30 -- superposition 30,24, 24 into 30, unify on (0).2 in 24 and (0).1.2.1 in 30
  have eq2683 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq1693 eq21 -- superposition 21,1693, 1693 into 21, unify on (0).2 in 1693 and (0).2.2.2 in 21
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2760 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2846 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1436 -- superposition 1436,11, 11 into 1436, unify on (0).2 in 11 and (0).1.2.1.2 in 1436
  have eq2902 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1518 -- superposition 1518,21, 21 into 1518, unify on (0).2 in 21 and (0).1 in 1518
  have eq3015 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2902 eq2760 -- backward demodulation 2760,2902
  have eq3016 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2902 eq2688 -- backward demodulation 2688,2902
  have eq3017 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2902 eq1874 -- backward demodulation 1874,2902
  have eq3019 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3015 -- forward demodulation 3015,11
  have eq3020 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3023 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X3 := superpose eq3017 eq1698 -- backward demodulation 1698,3017
  have eq3027 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3017 eq2846 -- backward demodulation 2846,3017
  have eq3160 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3020 eq3019 -- superposition 3019,3020, 3020 into 3019, unify on (0).2 in 3020 and (0).1.2 in 3019
  have eq3183 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3020 eq30 -- superposition 30,3020, 3020 into 30, unify on (0).2 in 3020 and (0).1.2.1 in 30
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3160 eq3027 -- backward demodulation 3027,3160
  have eq3251 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3017 eq3183 -- forward demodulation 3183,3017
  have eq3257 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := superpose eq3251 eq2683 -- backward demodulation 2683,3251
  have eq3302 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3250 eq55 -- superposition 55,3250, 3250 into 55, unify on (0).2 in 3250 and (0).2.2 in 55
  have eq3303 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3250 eq271 -- superposition 271,3250, 3250 into 271, unify on (0).2 in 3250 and (0).2.2.1 in 271
  have eq3315 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3302 eq3303 -- forward demodulation 3303,3302
  have eq3330 (X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq3315 eq3257 -- backward demodulation 3257,3315
  have eq3434 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq3330 eq390 -- backward demodulation 390,3330
  have eq3449 (X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ X2) ◇ X4)) ◇ X2))) = X2 := superpose eq3330 eq743 -- backward demodulation 743,3330
  have eq3546 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ ((X6 ◇ (X2 ◇ X6)) ◇ (X4 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)))) := superpose eq3330 eq2286 -- backward demodulation 2286,3330
  have eq3694 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) = X0 := superpose eq3302 eq3434 -- forward demodulation 3434,3302
  have eq3836 (X0 X1 X2 X5 X6 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X5)) ◇ (X6 ◇ (X2 ◇ X6))) := superpose eq3330 eq3546 -- forward demodulation 3546,3330
  have eq3859 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4))) := superpose eq3836 eq34 -- backward demodulation 34,3836
  have eq4293 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ (X2 ◇ X3))) = X3 := superpose eq1518 eq3694 -- superposition 3694,1518, 1518 into 3694, unify on (0).2 in 1518 and (0).1.2.1 in 3694
  have eq4635 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq3859 eq3859 -- superposition 3859,3859, 3859 into 3859, unify on (0).2 in 3859 and (0).2.2.2 in 3859
  have eq4740 (X0 X2 X3 X4 X5 X6 : G) : (X2 ◇ X6) = ((X2 ◇ X6) ◇ (X3 ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X4)) ◇ X3))) := superpose eq3836 eq4635 -- forward demodulation 4635,3836
  have eq4745 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2))) := superpose eq4740 eq105 -- backward demodulation 105,4740
  have eq4758 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq4745 eq1172 -- backward demodulation 1172,4745
  have eq4761 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq4758 eq3449 -- backward demodulation 3449,4758
  have eq4851 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X2 := superpose eq1518 eq4761 -- superposition 4761,1518, 1518 into 4761, unify on (0).2 in 1518 and (0).1.2 in 4761
  have eq4879 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4)) ◇ X5) := superpose eq4851 eq1135 -- backward demodulation 1135,4851
  have eq4880 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ ((X6 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4851 eq1140 -- backward demodulation 1140,4851
  have eq4885 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ X0) := superpose eq4851 eq1518 -- backward demodulation 1518,4851
  have eq4917 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X3 := superpose eq4885 eq4293 -- backward demodulation 4293,4885
  have eq4948 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq4917 eq3023 -- backward demodulation 3023,4917
  have eq5239 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))))) := superpose eq4948 eq4880 -- backward demodulation 4880,4948
  have eq6019 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ (X4 ◇ (X5 ◇ (X6 ◇ X5)))) := superpose eq4948 eq5239 -- forward demodulation 5239,4948
  have eq6020 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X4) := superpose eq4948 eq6019 -- forward demodulation 6019,4948
  have eq6025 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) = ((X4 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0))) ◇ X5) := superpose eq6020 eq4879 -- backward demodulation 4879,6020
  have eq6042 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq4948 eq6025 -- forward demodulation 6025,4948
  have eq6514 : sK0 ≠ ((sK0 ◇ sK2) ◇ sK2) := superpose eq6042 eq10 -- backward demodulation 10,6042
  have eq6515 : sK0 ≠ (sK0 ◇ sK2) := superpose eq6042 eq6514 -- forward demodulation 6514,6042
  subsumption eq6515 eq6042


@[equational_result]
theorem Equation650_implies_Equation3926 (G : Type*) [Magma G] (h : Equation650 G) : Equation3926 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
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
  have eq1434 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1435 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1437 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1519 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1435 eq1434 -- backward demodulation 1434,1435
  have eq1579 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1580 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1694 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1696 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1580 -- forward demodulation 1580,11
  have eq1875 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1696 -- superposition 1696,31, 31 into 1696, unify on (0).2 in 31 and (0).2.2.2 in 1696
  have eq1879 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1696 eq9 -- superposition 9,1696, 1696 into 9, unify on (0).2 in 1696 and (0).1.2.2 in 9
  have eq1884 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1696 eq12 -- superposition 12,1696, 1696 into 12, unify on (0).2 in 1696 and (0).1.2.1.2 in 12
  have eq2684 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1694 eq12 -- superposition 12,1694, 1694 into 12, unify on (0).2 in 1694 and (0).1.2.1.2 in 12
  have eq2689 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1879 -- superposition 1879,31, 31 into 1879, unify on (0).2 in 31 and (0).2.2.1.2 in 1879
  have eq2761 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1884 -- superposition 1884,31, 31 into 1884, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1884
  have eq2847 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1437 -- superposition 1437,11, 11 into 1437, unify on (0).2 in 11 and (0).1.2.1.2 in 1437
  have eq2903 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1519 -- superposition 1519,21, 21 into 1519, unify on (0).2 in 21 and (0).1 in 1519
  have eq3016 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2903 eq2761 -- backward demodulation 2761,2903
  have eq3017 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2903 eq2689 -- backward demodulation 2689,2903
  have eq3018 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2903 eq1875 -- backward demodulation 1875,2903
  have eq3020 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3021 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3017 -- forward demodulation 3017,11
  have eq3028 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3018 eq2847 -- backward demodulation 2847,3018
  have eq3161 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3021 eq3020 -- superposition 3020,3021, 3021 into 3020, unify on (0).2 in 3021 and (0).1.2 in 3020
  have eq3181 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3021 eq372 -- superposition 372,3021, 3021 into 372, unify on (0).2 in 3021 and (0).1.2.1.1 in 372
  have eq3227 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3021 eq30 -- superposition 30,3021, 3021 into 30, unify on (0).2 in 3021 and (0).1.2.1 in 30
  have eq3251 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3161 eq3028 -- backward demodulation 3028,3161
  have eq3253 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3018 eq3227 -- forward demodulation 3227,3018
  have eq3256 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3253 eq2684 -- backward demodulation 2684,3253
  have eq3301 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3251 eq55 -- superposition 55,3251, 3251 into 55, unify on (0).2 in 3251 and (0).2.2 in 55
  have eq3302 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3251 eq271 -- superposition 271,3251, 3251 into 271, unify on (0).2 in 3251 and (0).2.2.1 in 271
  have eq3311 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3301 eq3181 -- backward demodulation 3181,3301
  have eq3313 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3301 eq3302 -- forward demodulation 3302,3301
  have eq3327 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3313 eq3256 -- backward demodulation 3256,3313
  have eq3414 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq33 -- superposition 33,3313, 3313 into 33, unify on (0).2 in 3313 and (0).1.2.1 in 33
  have eq3458 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3313 eq9 -- superposition 9,3313, 3313 into 9, unify on (0).2 in 3313 and (0).1.2 in 9
  have eq3535 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3313 eq21 -- superposition 21,3313, 3313 into 21, unify on (0).2 in 3313 and (0).1 in 21
  have eq3593 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3313 eq3414 -- forward demodulation 3414,3313
  have eq3658 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3313 eq3458 -- superposition 3458,3313, 3313 into 3458, unify on (0).2 in 3313 and (0).1.2 in 3458
  have eq3681 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3458 eq3313 -- superposition 3313,3458, 3458 into 3313, unify on (0).2 in 3458 and (0).1 in 3313
  have eq3859 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3658 eq3311 -- backward demodulation 3311,3658
  have eq4094 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3859 eq11 -- superposition 11,3859, 3859 into 11, unify on (0).2 in 3859 and (0).1.2.1 in 11
  have eq4200 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3859 eq3681 -- superposition 3681,3859, 3859 into 3681, unify on (0).2 in 3859 and (0).1.2.2 in 3681
  have eq4236 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4200 eq4094 -- backward demodulation 4094,4200
  have eq4791 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4236 eq3535 -- backward demodulation 3535,4236
  have eq5350 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4236 eq3327 -- backward demodulation 3327,4236
  have eq5896 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5350 eq4791 -- backward demodulation 4791,5350
  have eq5929 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5896 eq3593 -- backward demodulation 3593,5896
  have eq5948 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3658 eq5929 -- forward demodulation 5929,3658
  have eq5956 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5948 eq3681 -- backward demodulation 3681,5948
  have eq5970 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK2) := superpose eq5948 eq10 -- backward demodulation 10,5948
  have eq5978 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5956 eq5970 -- forward demodulation 5970,5956
  subsumption eq5978 eq5956


@[equational_result]
theorem Equation448_implies_Equation441 (G : Type*) [Magma G] (h : Equation448 G) : Equation441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation448_implies_Equation4515 (G : Type*) [Magma G] (h : Equation448 G) : Equation4515 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation630 (G : Type*) [Magma G] (h : Equation448 G) : Equation630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation448_implies_Equation3869 (G : Type*) [Magma G] (h : Equation448 G) : Equation3869 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK2) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3868 (G : Type*) [Magma G] (h : Equation448 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation381 (G : Type*) [Magma G] (h : Equation448 G) : Equation381 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation448_implies_Equation640 (G : Type*) [Magma G] (h : Equation448 G) : Equation640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation448_implies_Equation3924 (G : Type*) [Magma G] (h : Equation448 G) : Equation3924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3671 (G : Type*) [Magma G] (h : Equation448 G) : Equation3671 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3712 (G : Type*) [Magma G] (h : Equation448 G) : Equation3712 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3669 (G : Type*) [Magma G] (h : Equation448 G) : Equation3669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK0) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3917 (G : Type*) [Magma G] (h : Equation448 G) : Equation3917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3740 (G : Type*) [Magma G] (h : Equation448 G) : Equation3740 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation3716 (G : Type*) [Magma G] (h : Equation448 G) : Equation3716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq16 : sK0 ≠ (sK0 ◇ sK1) := superpose eq12 eq15 -- forward demodulation 15,12
  subsumption eq16 eq12


@[equational_result]
theorem Equation448_implies_Equation1267 (G : Type*) [Magma G] (h : Equation448 G) : Equation1267 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK2) ◇ sK2) ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation2567_implies_Equation3210 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3210 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK2) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq26


@[equational_result]
theorem Equation2567_implies_Equation2990 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2990 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation1681 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1681 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.1.2 in 9
  have eq29 : sK0 ≠ sK0 := superpose eq18 eq17 -- superposition 17,18, 18 into 17, unify on (0).2 in 18 and (0).2 in 17
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation1634 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1634 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


@[equational_result]
theorem Equation2567_implies_Equation1248 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1248 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


@[equational_result]
theorem Equation2567_implies_Equation3533 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation3075 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq26


@[equational_result]
theorem Equation2567_implies_Equation4155 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation1691 (G : Type*) [Magma G] (h : Equation2567 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 eq26


@[equational_result]
theorem Equation2567_implies_Equation2973 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2973 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


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
theorem Equation2567_implies_Equation4192 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4192 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation2919 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2919 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq25 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq27 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq33 : sK0 ≠ sK0 := superpose eq27 eq25 -- superposition 25,27, 27 into 25, unify on (0).2 in 27 and (0).2 in 25
  subsumption eq33 rfl


@[equational_result]
theorem Equation2567_implies_Equation3122 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3122 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3024 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3024 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3512 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq26 eq10 -- backward demodulation 10,26
  subsumption eq29 rfl


@[equational_result]
theorem Equation2567_implies_Equation364 (G : Type*) [Magma G] (h : Equation2567 G) : Equation364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation2567_implies_Equation2770 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2770 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq15 rfl


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
theorem Equation2567_implies_Equation832 (G : Type*) [Magma G] (h : Equation2567 G) : Equation832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


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
theorem Equation2567_implies_Equation4385 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 : sK0 ≠ (sK0 ◇ sK0) := superpose eq26 eq27 -- forward demodulation 27,26
  subsumption eq30 eq20


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
theorem Equation2567_implies_Equation4118 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq13 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).1.1 in 11
  have eq17 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq17 rfl


@[equational_result]
theorem Equation2567_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2909 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq32 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation2567_implies_Equation3055 (G : Type*) [Magma G] (h : Equation2567 G) : Equation3055 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation2567_implies_Equation4100 (G : Type*) [Magma G] (h : Equation2567 G) : Equation4100 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.2.1 in 9
  have eq12 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq20 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq26 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X2 := superpose eq20 eq11 -- backward demodulation 11,20
  have eq27 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  subsumption eq27 eq26


@[equational_result]
theorem Equation3210_implies_Equation3159 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK1 ◇ sK2) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation619 (G : Type*) [Magma G] (h : Equation3210 G) : Equation619 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq12 eq10 -- backward demodulation 10,12
  have eq17 : sK0 ≠ (sK0 ◇ sK0) := superpose eq13 eq15 -- backward demodulation 15,13
  subsumption eq17 eq13


@[equational_result]
theorem Equation3210_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3461 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 rfl


@[equational_result]
theorem Equation3210_implies_Equation3085 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3085 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3210_implies_Equation2530 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2530 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation3210_implies_Equation2493 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2493 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation3210_implies_Equation2456 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq15 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq15 eq12


@[equational_result]
theorem Equation3210_implies_Equation2946 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2946 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3674 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation1884 (G : Type*) [Magma G] (h : Equation3210 G) : Equation1884 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation2733 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2733 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3877 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation2124 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq13 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq16 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq16 eq12


@[equational_result]
theorem Equation3210_implies_Equation2936 (G : Type*) [Magma G] (h : Equation3210 G) : Equation2936 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq18 : sK0 ≠ sK0 := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3159_implies_Equation2567 (G : Type*) [Magma G] (h : Equation3159 G) : Equation2567 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK2 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq12 eq13 -- superposition 13,12, 12 into 13, unify on (0).2 in 12 and (0).1.1.1 in 13
  have eq18 : sK0 ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq14 eq10 -- backward demodulation 10,14
  subsumption eq18 eq14


@[equational_result]
theorem Equation3159_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3159 G) : Equation3112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3159_implies_Equation2852 (G : Type*) [Magma G] (h : Equation3159 G) : Equation2852 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq12 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq12 eq9 -- backward demodulation 9,12
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation2836_implies_Equation2430 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2430 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK3))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq42 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2836_implies_Equation246 (G : Type*) [Magma G] (h : Equation2836 G) : Equation246 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq26 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq26 rfl


@[equational_result]
theorem Equation2836_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq42 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq42 rfl


@[equational_result]
theorem Equation2836_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2364 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X5) = X5 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X3 := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).1.1.2 in 11
  have eq42 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq42 rfl


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
theorem Equation281_implies_Equation66 (G : Type*) [Magma G] (h : Equation281 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.1.1 in 9
  have eq13 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1 in 12
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2.1 in 14
  have eq24 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq18 eq13 -- backward demodulation 13,18
  have eq33 : sK0 ≠ sK0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq33 rfl


@[equational_result]
theorem Equation177_implies_Equation170 (G : Type*) [Magma G] (h : Equation177 G) : Equation170 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2 in 9
  have eq17 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ X0) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1.1 in 12
  have eq21 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq23 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.1.1 in 21
  have eq50 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation170_implies_Equation47 (G : Type*) [Magma G] (h : Equation170 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1 in 8
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq14 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).1.1 in 8
  have eq16 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2.2.1 in 10
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq16 eq14 -- backward demodulation 14,16
  have eq26 : sK0 ≠ sK0 := superpose eq20 eq9 -- superposition 9,20, 20 into 9, unify on (0).2 in 20 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation170_implies_Equation255 (G : Type*) [Magma G] (h : Equation170 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq15 : sK0 ≠ sK0 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation170_implies_Equation66 (G : Type*) [Magma G] (h : Equation170 G) : Equation66 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq29 : sK0 ≠ sK0 := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2 in 10
  subsumption eq29 rfl


@[equational_result]
theorem Equation170_implies_Equation177 (G : Type*) [Magma G] (h : Equation170 G) : Equation177 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.1 in 9
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).1.1 in 9
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.2.1 in 11
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq17 eq15 -- backward demodulation 15,17
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).1.2.2 in 21
  have eq50 : sK0 ≠ sK0 := superpose eq23 eq10 -- superposition 10,23, 23 into 10, unify on (0).2 in 23 and (0).2 in 10
  subsumption eq50 rfl


@[equational_result]
theorem Equation66_implies_Equation170 (G : Type*) [Magma G] (h : Equation66 G) : Equation170 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ X0) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1.1 in 16
  have eq24 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq24 -- superposition 24,11, 11 into 24, unify on (0).2 in 11 and (0).1.1.1 in 24
  have eq40 : sK0 ≠ sK0 := superpose eq26 eq10 -- superposition 10,26, 26 into 10, unify on (0).2 in 26 and (0).2 in 10
  subsumption eq40 rfl


@[equational_result]
theorem Equation66_implies_Equation281 (G : Type*) [Magma G] (h : Equation66 G) : Equation281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).1.2.2 in 9
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2 in 12
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.2 in 12
  have eq18 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1.1 in 16
  have eq24 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq18 eq15 -- backward demodulation 15,18
  have eq31 : sK0 ≠ sK0 := superpose eq24 eq10 -- superposition 10,24, 24 into 10, unify on (0).2 in 24 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation749_implies_Equation2928 (G : Type*) [Magma G] (h : Equation749 G) : Equation2928 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation749_implies_Equation473 (G : Type*) [Magma G] (h : Equation749 G) : Equation473 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq213 : sK0 ≠ sK0 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2 in 10
  subsumption eq213 rfl


@[equational_result]
theorem Equation749_implies_Equation2293 (G : Type*) [Magma G] (h : Equation749 G) : Equation2293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq46 eq13 -- backward demodulation 13,46
  have eq81 : sK0 ≠ sK0 := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation749_implies_Equation639 (G : Type*) [Magma G] (h : Equation749 G) : Equation639 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq22 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq20 eq21 -- forward demodulation 21,20
  subsumption eq22 eq18


@[equational_result]
theorem Equation749_implies_Equation1316 (G : Type*) [Magma G] (h : Equation749 G) : Equation1316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose eq19 eq63 -- forward demodulation 63,19
  have eq66 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq19 eq65 -- forward demodulation 65,19
  subsumption eq66 eq18


@[equational_result]
theorem Equation749_implies_Equation2254 (G : Type*) [Magma G] (h : Equation749 G) : Equation2254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq46 eq13 -- backward demodulation 13,46
  have eq81 : sK0 ≠ sK0 := superpose eq58 eq10 -- superposition 10,58, 58 into 10, unify on (0).2 in 58 and (0).2 in 10
  subsumption eq81 rfl


@[equational_result]
theorem Equation749_implies_Equation2530 (G : Type*) [Magma G] (h : Equation749 G) : Equation2530 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq22 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := superpose eq20 eq21 -- forward demodulation 21,20
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq31 eq13 -- backward demodulation 13,31
  have eq50 : sK0 ≠ sK0 := superpose eq37 eq22 -- superposition 22,37, 37 into 22, unify on (0).2 in 37 and (0).2 in 22
  subsumption eq50 rfl


@[equational_result]
theorem Equation749_implies_Equation2338 (G : Type*) [Magma G] (h : Equation749 G) : Equation2338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq28 eq13 -- backward demodulation 13,28
  have eq45 : sK0 ≠ sK0 := superpose eq36 eq21 -- superposition 21,36, 36 into 21, unify on (0).2 in 36 and (0).2 in 21
  subsumption eq45 rfl


@[equational_result]
theorem Equation749_implies_Equation1113 (G : Type*) [Magma G] (h : Equation749 G) : Equation1113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq18


@[equational_result]
theorem Equation749_implies_Equation2855 (G : Type*) [Magma G] (h : Equation749 G) : Equation2855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation749_implies_Equation513 (G : Type*) [Magma G] (h : Equation749 G) : Equation513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq18


@[equational_result]
theorem Equation749_implies_Equation714 (G : Type*) [Magma G] (h : Equation749 G) : Equation714 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq22 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose eq19 eq21 -- forward demodulation 21,19
  subsumption eq22 eq18


@[equational_result]
theorem Equation749_implies_Equation3116 (G : Type*) [Magma G] (h : Equation749 G) : Equation3116 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq16


@[equational_result]
theorem Equation749_implies_Equation1239 (G : Type*) [Magma G] (h : Equation749 G) : Equation1239 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose eq46 eq63 -- forward demodulation 63,46
  have eq66 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq20 eq65 -- forward demodulation 65,20
  subsumption eq66 eq18


@[equational_result]
theorem Equation749_implies_Equation2300 (G : Type*) [Magma G] (h : Equation749 G) : Equation2300 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq28 eq13 -- backward demodulation 13,28
  have eq45 : sK0 ≠ sK0 := superpose eq36 eq21 -- superposition 21,36, 36 into 21, unify on (0).2 in 36 and (0).2 in 21
  subsumption eq45 rfl


@[equational_result]
theorem Equation749_implies_Equation2900 (G : Type*) [Magma G] (h : Equation749 G) : Equation2900 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq20 : sK0 ≠ sK0 := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq20 rfl


@[equational_result]
theorem Equation749_implies_Equation2865 (G : Type*) [Magma G] (h : Equation749 G) : Equation2865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq13


@[equational_result]
theorem Equation749_implies_Equation1229 (G : Type*) [Magma G] (h : Equation749 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq46 eq63 -- forward demodulation 63,46
  subsumption eq65 eq18


@[equational_result]
theorem Equation749_implies_Equation2444 (G : Type*) [Magma G] (h : Equation749 G) : Equation2444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq28 eq13 -- backward demodulation 13,28
  have eq45 : sK0 ≠ sK0 := superpose eq36 eq21 -- superposition 21,36, 36 into 21, unify on (0).2 in 36 and (0).2 in 21
  subsumption eq45 rfl


@[equational_result]
theorem Equation749_implies_Equation2534 (G : Type*) [Magma G] (h : Equation749 G) : Equation2534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq22 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq19 eq21 -- forward demodulation 21,19
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq29 eq13 -- backward demodulation 13,29
  have eq46 : sK0 ≠ sK0 := superpose eq37 eq22 -- superposition 22,37, 37 into 22, unify on (0).2 in 37 and (0).2 in 22
  subsumption eq46 rfl


@[equational_result]
theorem Equation749_implies_Equation2507 (G : Type*) [Magma G] (h : Equation749 G) : Equation2507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq20 eq10 -- backward demodulation 10,20
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq30 eq13 -- backward demodulation 13,30
  have eq49 : sK0 ≠ sK0 := superpose eq36 eq21 -- superposition 21,36, 36 into 21, unify on (0).2 in 36 and (0).2 in 21
  subsumption eq49 rfl


@[equational_result]
theorem Equation749_implies_Equation2940 (G : Type*) [Magma G] (h : Equation749 G) : Equation2940 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) := superpose eq19 eq10 -- backward demodulation 10,19
  subsumption eq21 eq13


@[equational_result]
theorem Equation749_implies_Equation1278 (G : Type*) [Magma G] (h : Equation749 G) : Equation1278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq9


@[equational_result]
theorem Equation749_implies_Equation3079 (G : Type*) [Magma G] (h : Equation749 G) : Equation3079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq46 eq13 -- backward demodulation 13,46
  have eq63 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose eq20 eq63 -- forward demodulation 63,20
  subsumption eq65 eq58


@[equational_result]
theorem Equation749_implies_Equation3068 (G : Type*) [Magma G] (h : Equation749 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq46 eq13 -- backward demodulation 13,46
  have eq63 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := superpose eq46 eq63 -- forward demodulation 63,46
  subsumption eq65 eq58


@[equational_result]
theorem Equation749_implies_Equation3056 (G : Type*) [Magma G] (h : Equation749 G) : Equation3056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq16


@[equational_result]
theorem Equation749_implies_Equation3105 (G : Type*) [Magma G] (h : Equation749 G) : Equation3105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X2 := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).1.1.2 in 16
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X2 := superpose eq46 eq43 -- backward demodulation 43,46
  have eq63 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := superpose eq46 eq10 -- backward demodulation 10,46
  have eq65 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := superpose eq46 eq63 -- forward demodulation 63,46
  subsumption eq65 eq57


@[equational_result]
theorem Equation749_implies_Equation2503 (G : Type*) [Magma G] (h : Equation749 G) : Equation2503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq28 eq13 -- backward demodulation 13,28
  have eq45 : sK0 ≠ sK0 := superpose eq36 eq21 -- superposition 21,36, 36 into 21, unify on (0).2 in 36 and (0).2 in 21
  subsumption eq45 rfl


@[equational_result]
theorem Equation749_implies_Equation1109 (G : Type*) [Magma G] (h : Equation749 G) : Equation1109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq18


@[equational_result]
theorem Equation749_implies_Equation1023 (G : Type*) [Magma G] (h : Equation749 G) : Equation1023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.1 in 9
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := superpose eq11 eq16 -- superposition 16,11, 11 into 16, unify on (0).2 in 11 and (0).1.1 in 16
  have eq63 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq46 eq10 -- backward demodulation 10,46
  subsumption eq63 eq18


@[equational_result]
theorem Equation749_implies_Equation1026 (G : Type*) [Magma G] (h : Equation749 G) : Equation1026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.1.1 in 13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq21 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose eq19 eq10 -- backward demodulation 10,19
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq16 eq13 -- superposition 13,16, 16 into 13, unify on (0).2 in 16 and (0).1.1 in 13
  have eq38 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := superpose eq28 eq21 -- backward demodulation 21,28
  subsumption eq38 eq18


