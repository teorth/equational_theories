import equational_theories.Equations.All
import equational_theories.Superposition

namespace Sheffer

open Sheffer

theorem Equation345169_implies_GeneralAxiom1 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x = (x ◇ y) ◇ (x ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain  ⟨sK0, sK1, nh ⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq180 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq185 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq180 eq28 -- superposition 28,180, 180 into 28, unify on (0).2 in 180 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq180 eq548 -- forward demodulation 548,180
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq185 eq1150 -- forward demodulation 1150,185
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1832 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1854 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1832 -- forward demodulation 1832,1184
  have eq2075 : sK0 ≠ sK0 := superpose eq1854 eq8 -- superposition 8,1854, 1854 into 8, unify on (0).2 in 1854 and (0).2 in 8
  subsumption eq2075 rfl

theorem Equation345169_implies_Axiom2Auto (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y)):= by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.2.1 in 10
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11 -- superposition 11,7, 7 into 11, unify on (0).2 in 7 and (0).1.2.1 in 11
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X2 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq11 eq7 -- superposition 7,11, 11 into 7, unify on (0).2 in 11 and (0).1.1.2.1 in 7
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq255 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq182 eq12 -- superposition 12,182, 182 into 12, unify on (0).2 in 182 and (0).2.1.1 in 12
  have eq280 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq108 eq255 -- forward demodulation 255,108
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq530 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq127 eq127 -- superposition 127,127, 127 into 127, unify on (0).2 in 127 and (0).1.1.2.1 in 127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq553 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq127 eq14 -- superposition 14,127, 127 into 14, unify on (0).2 in 127 and (0).1.1.2.1 in 14
  have eq554 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq127 eq28 -- superposition 28,127, 127 into 28, unify on (0).2 in 127 and (0).1.2.1 in 28
  have eq570 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq578 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq177 eq530 -- forward demodulation 530,177
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq606 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq553 -- forward demodulation 553,177
  have eq608 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq606 eq33 -- backward demodulation 33,606
  have eq671 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq177 eq554 -- forward demodulation 554,177
  have eq672 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq108 eq671 -- forward demodulation 671,108
  have eq679 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq570 -- forward demodulation 570,177
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1188 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq1184 eq23 -- backward demodulation 23,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq1854 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq1853 eq280 -- backward demodulation 280,1853
  have eq2068 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq1853 -- superposition 1853,7, 7 into 1853, unify on (0).2 in 7 and (0).1.2 in 1853
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2137 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq108 eq2068 -- forward demodulation 2068,108
  have eq2138 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq2137 eq1854 -- backward demodulation 1854,2137
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2161 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq2149 eq127 -- backward demodulation 127,2149
  have eq2172 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2149 eq578 -- backward demodulation 578,2149
  have eq2173 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq2149 eq606 -- backward demodulation 606,2149
  have eq2175 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq2149 eq608 -- backward demodulation 608,2149
  have eq2198 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq672 -- backward demodulation 672,2149
  have eq2202 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq679 -- backward demodulation 679,2149
  have eq2223 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq1188 -- backward demodulation 1188,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2439 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) := superpose eq2149 eq2175 -- forward demodulation 2175,2149
  have eq2497 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2202 -- forward demodulation 2202,2149
  have eq2536 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq2223 -- forward demodulation 2223,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3156 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq2374 eq2374 -- superposition 2374,2374, 2374 into 2374, unify on (0).2 in 2374 and (0).1.1 in 2374
  have eq3233 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq2198 eq2536 -- superposition 2536,2198, 2198 into 2536, unify on (0).2 in 2198 and (0).1.1.1 in 2536
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3546 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq2149 -- backward demodulation 2149,3523
  have eq3547 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq3523 eq2173 -- backward demodulation 2173,3523
  have eq3637 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3546 eq503 -- backward demodulation 503,3546
  have eq3664 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2374 eq3523 -- superposition 3523,2374, 2374 into 3523, unify on (0).2 in 2374 and (0).1 in 3523
  have eq3681 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq3523 eq2150 -- superposition 2150,3523, 3523 into 2150, unify on (0).2 in 3523 and (0).1.1 in 2150
  have eq4349 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1.1 in 2497
  have eq5559 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq887 eq3233 -- superposition 3233,887, 887 into 3233, unify on (0).2 in 887 and (0).1.1.1 in 3233
  have eq7101 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3664 eq2742 -- superposition 2742,3664, 3664 into 2742, unify on (0).2 in 3664 and (0).2.2 in 2742
  have eq7372 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq2374 eq2439 -- superposition 2439,2374, 2374 into 2439, unify on (0).2 in 2374 and (0).2.2 in 2439
  have eq7638 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq3637 eq3681 -- superposition 3681,3637, 3637 into 3681, unify on (0).2 in 3637 and (0).1.2 in 3681
  have eq7766 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7101 eq7638 -- forward demodulation 7638,7101
  have eq10409 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3637 eq4349 -- superposition 4349,3637, 3637 into 4349, unify on (0).2 in 3637 and (0).1.1 in 4349
  have eq10625 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7101 eq10409 -- forward demodulation 10409,7101
  have eq19499 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq7101 -- superposition 7101,3523, 3523 into 7101, unify on (0).2 in 3523 and (0).2 in 7101
  have eq20824 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7766 eq3547 -- superposition 3547,7766, 7766 into 3547, unify on (0).2 in 7766 and (0).1 in 3547
  have eq20969 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq5559 eq20824 -- forward demodulation 20824,5559
  have eq24348 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2161 eq10625 -- superposition 10625,2161, 2161 into 10625, unify on (0).2 in 2161 and (0).2.2 in 10625
  have eq24909 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2138 eq24348 -- forward demodulation 24348,2138
  have eq35896 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7372 eq3156 -- superposition 3156,7372, 7372 into 3156, unify on (0).2 in 7372 and (0).2.2 in 3156
  have eq36144 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq7372 eq20969 -- superposition 20969,7372, 7372 into 20969, unify on (0).2 in 7372 and (0).1.1 in 20969
  have eq36219 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7766 eq36144 -- forward demodulation 36144,7766
  have eq60979 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq2172 eq7766 -- superposition 7766,2172, 2172 into 7766, unify on (0).2 in 2172 and (0).2.2 in 7766
  have eq61095 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq24909 eq60979 -- forward demodulation 60979,24909
  have eq61098 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq61095 eq36219 -- backward demodulation 36219,61095
  have eq62904 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq35896 eq19499 -- superposition 19499,35896, 35896 into 19499, unify on (0).2 in 35896 and (0).2.2.2 in 19499
  have eq63178 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq7766 eq62904 -- forward demodulation 62904,7766
  have eq63179 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq61098 eq63178 -- forward demodulation 63178,61098
  have eq67699 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq63179 eq8 -- superposition 8,63179, 63179 into 8, unify on (0).2 in 63179 and (0).2 in 8
  subsumption eq67699 rfl

theorem Equation345169_implies_Comm (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ y = y ◇ x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3716 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq3523 eq8 -- superposition 8,3523, 3523 into 8, unify on (0).2 in 3523 and (0).2 in 8
  subsumption eq3716 rfl

theorem Equation345169_implies_Helper1 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, (x ◇ x) ◇ (y ◇ x) = x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.1.2.1 in 8
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).1.1.1 in 11
  have eq29 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.1.1 in 12
  have eq77 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2.2.2 in 10
  have eq107 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq17 -- superposition 17,10, 10 into 17, unify on (0).2 in 10 and (0).1.2 in 17
  have eq109 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2.2 in 10
  have eq126 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq17 eq107 -- forward demodulation 107,17
  have eq128 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq109 eq126 -- backward demodulation 126,109
  have eq181 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq109 eq8 -- superposition 8,109, 109 into 8, unify on (0).2 in 109 and (0).1.1 in 8
  have eq186 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq109 eq8 -- superposition 8,109, 109 into 8, unify on (0).2 in 109 and (0).1.2 in 8
  have eq374 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq181 eq29 -- superposition 29,181, 181 into 29, unify on (0).2 in 181 and (0).1.2.1 in 29
  have eq458 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq8 eq77 -- superposition 77,8, 8 into 77, unify on (0).2 in 8 and (0).2.2 in 77
  have eq502 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq109 eq458 -- forward demodulation 458,109
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq502 eq374 -- backward demodulation 374,502
  have eq504 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq128 eq503 -- forward demodulation 503,128
  have eq553 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq128 eq29 -- superposition 29,128, 128 into 29, unify on (0).2 in 128 and (0).1.2.1 in 29
  have eq578 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq128 eq77 -- superposition 77,128, 128 into 77, unify on (0).2 in 128 and (0).2.2.2.2.1 in 77
  have eq664 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq181 eq553 -- forward demodulation 553,181
  have eq665 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq109 eq664 -- forward demodulation 664,109
  have eq678 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq181 eq578 -- forward demodulation 578,181
  have eq679 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq109 eq678 -- forward demodulation 678,109
  have eq680 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq504 eq679 -- forward demodulation 679,504
  have eq824 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq8 eq680 -- superposition 680,8, 8 into 680, unify on (0).2 in 8 and (0).1 in 680
  have eq888 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq109 eq824 -- forward demodulation 824,109
  have eq1119 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq888 eq29 -- superposition 29,888, 888 into 29, unify on (0).2 in 888 and (0).1.2.1 in 29
  have eq1155 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq888 eq128 -- superposition 128,888, 888 into 128, unify on (0).2 in 888 and (0).1.1.2.1 in 128
  have eq1170 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq186 eq1155 -- forward demodulation 1155,186
  have eq1171 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1170 eq1119 -- backward demodulation 1119,1170
  have eq1185 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq128 eq1171 -- forward demodulation 1171,128
  have eq1626 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).1.1 in 1185
  have eq1833 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1626 eq128 -- superposition 128,1626, 1626 into 128, unify on (0).2 in 1626 and (0).1.1.2.1 in 128
  have eq1856 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1185 eq1833 -- forward demodulation 1833,1185
  have eq2080 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1856 eq12 -- superposition 12,1856, 1856 into 12, unify on (0).2 in 1856 and (0).2.1.2.1 in 12
  have eq2154 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq181 eq2080 -- forward demodulation 2080,181
  have eq2205 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2154 eq665 -- backward demodulation 665,2154
  have eq2945 : sK0 ≠ sK0 := superpose eq2205 eq9 -- superposition 9,2205, 2205 into 9, unify on (0).2 in 2205 and (0).2 in 9
  subsumption eq2945 rfl

theorem Equation345169_implies_Helper2 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ (y ◇ (x ◇ x)) = x ◇ x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1578 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose eq1185 eq600 -- superposition 600,1185, 1185 into 600, unify on (0).2 in 1185 and (0).2.2 in 600
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2318 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq2149 eq1578 -- backward demodulation 1578,2149
  have eq5294 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq2318 eq8 -- superposition 8,2318, 2318 into 8, unify on (0).2 in 2318 and (0).2 in 8
  subsumption eq5294 rfl

theorem Equation345169_implies_Helper3 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x = (x ◇ (y ◇ z)) ◇ (x ◇ z) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8  : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3681 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq3523 eq2150 -- superposition 2150,3523, 3523 into 2150, unify on (0).2 in 3523 and (0).1.1 in 2150
  have eq3714  : sK0 ≠ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq3523 eq8 -- superposition 8,3523, 3523 into 8, unify on (0).2 in 3523 and (0).2 in 8
  subsumption eq3714 eq3681

theorem Equation345169_implies_Helper4 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ (x ◇ (y ◇ z))) = x ◇ (y ◇ z) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11 -- superposition 11,7, 7 into 11, unify on (0).2 in 7 and (0).1.2.1 in 11
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq554 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq127 eq28 -- superposition 28,127, 127 into 28, unify on (0).2 in 127 and (0).1.2.1 in 28
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq671 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq177 eq554 -- forward demodulation 554,177
  have eq672 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq108 eq671 -- forward demodulation 671,108
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1188 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq1184 eq23 -- backward demodulation 23,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2198 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq672 -- backward demodulation 672,2149
  have eq2223 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq1188 -- backward demodulation 1188,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2536 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq2223 -- forward demodulation 2223,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3560 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X0 ◇ X1)) = X1 := superpose eq3523 eq2536 -- backward demodulation 2536,3523
  have eq3705 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3523 eq2374 -- superposition 2374,3523, 3523 into 2374, unify on (0).2 in 3523 and (0).1.1 in 2374
  have eq3799 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X2 := superpose eq2198 eq3560 -- superposition 3560,2198, 2198 into 3560, unify on (0).2 in 2198 and (0).1.1.2 in 3560
  have eq9738 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq3705 eq3799 -- superposition 3799,3705, 3705 into 3799, unify on (0).2 in 3705 and (0).1.1 in 3799
  have eq324521 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq9738 eq8 -- superposition 8,9738, 9738 into 8, unify on (0).2 in 9738 and (0).2 in 8
  subsumption eq324521 rfl

theorem Equation345169_implies_Helper5 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ (x ◇ z))) ◇ y = y ◇ (z ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2346 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2713 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2346 -- forward demodulation 2346,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3629 : (sK1 ◇ (sK0 ◇ sK2)) ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK1) := superpose eq3523 eq8 -- backward demodulation 8,3523
  have eq3706 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq3523 eq2713 -- superposition 2713,3523, 3523 into 2713, unify on (0).2 in 3523 and (0).1 in 2713
  have eq211471 : (sK1 ◇ (sK0 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := superpose eq3706 eq3629 -- superposition 3629,3706, 3706 into 3629, unify on (0).2 in 3706 and (0).2 in 3629
  subsumption eq211471 rfl

theorem Equation345169_implies_Helper6 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z w : G, (x ◇ y) ◇ (z ◇ w) = (w ◇ z) ◇ (y ◇ x):= by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ≠ ((sK3 ◇ sK2) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3629 : ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ≠ ((sK3 ◇ sK2) ◇ (sK0 ◇ sK1)) := superpose eq3523 eq8 -- backward demodulation 8,3523
  have eq3649 : ((sK0 ◇ sK1) ◇ (sK2 ◇ sK3)) ≠ ((sK2 ◇ sK3) ◇ (sK0 ◇ sK1)) := superpose eq3523 eq3629 -- forward demodulation 3629,3523
  subsumption eq3649 eq3523

theorem Equation345169_implies_Helper7 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ y) ◇ z = z ◇ (y ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq180 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq185 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq180 eq28 -- superposition 28,180, 180 into 28, unify on (0).2 in 180 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq180 eq548 -- forward demodulation 548,180
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq185 eq1150 -- forward demodulation 1150,185
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1832 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1854 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1832 -- forward demodulation 1832,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1854 eq11 -- superposition 11,1854, 1854 into 11, unify on (0).2 in 1854 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq180 eq2075 -- forward demodulation 2075,180
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq185 eq2742 -- superposition 2742,185, 185 into 2742, unify on (0).2 in 185 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3629 : ((sK0 ◇ sK1) ◇ sK2) ≠ (sK2 ◇ (sK0 ◇ sK1)) := superpose eq3523 eq8 -- backward demodulation 8,3523
  subsumption eq3629 eq3523

theorem Equation345169_implies_Helper8 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, (x ◇ (y ◇ x)) ◇ y = y ◇ y := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh ⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8  : ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ≠ (sK1 ◇ sK1) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2346 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2713 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2346 -- forward demodulation 2346,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3629 : (sK1 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose eq3523 eq8 -- backward demodulation 8,3523
  have eq3700 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3523 eq2150 -- superposition 2150,3523, 3523 into 2150, unify on (0).2 in 3523 and (0).1.2 in 2150
  have eq8965 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3700 eq2713 -- superposition 2713,3700, 3700 into 2713, unify on (0).2 in 3700 and (0).2.1 in 2713
  have eq9079 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3523 eq8965 -- forward demodulation 8965,3523
  have eq21880 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose eq9079 eq3629 -- superposition 3629,9079, 9079 into 3629, unify on (0).2 in 9079 and (0).2 in 3629
  subsumption eq21880 rfl

theorem Equation345169_implies_Helper9 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (y ◇ x) = x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3629 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := superpose eq3523 eq8 -- backward demodulation 8,3523
  have eq3707 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3523 eq2374 -- superposition 2374,3523, 3523 into 2374, unify on (0).2 in 3523 and (0).1.1 in 2374
  have eq9700 : sK0 ≠ sK0 := superpose eq3707 eq3629 -- superposition 3629,3707, 3707 into 3629, unify on (0).2 in 3707 and (0).2 in 3629
  subsumption eq9700 rfl

theorem Equation345169_implies_Helper10 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ (y ◇ (x ◇ y)) = x ◇ x := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq570 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq679 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq570 -- forward demodulation 570,177
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1578 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose eq1185 eq600 -- superposition 600,1185, 1185 into 600, unify on (0).2 in 1185 and (0).2.2 in 600
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2202 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq679 -- backward demodulation 679,2149
  have eq2318 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq2149 eq1578 -- backward demodulation 1578,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2497 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2202 -- forward demodulation 2202,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3546 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq2149 -- backward demodulation 2149,3523
  have eq3637 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3546 eq503 -- backward demodulation 503,3546
  have eq3664 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2374 eq3523 -- superposition 3523,2374, 2374 into 3523, unify on (0).2 in 2374 and (0).1 in 3523
  have eq4349 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1.1 in 2497
  have eq7101 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3664 eq2742 -- superposition 2742,3664, 3664 into 2742, unify on (0).2 in 3664 and (0).2.2 in 2742
  have eq10409 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3637 eq4349 -- superposition 4349,3637, 3637 into 4349, unify on (0).2 in 3637 and (0).1.1 in 4349
  have eq10625 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7101 eq10409 -- forward demodulation 10409,7101
  have eq10626 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose eq10625 eq8 -- backward demodulation 8,10625
  subsumption eq10626 eq2318

theorem Equation345169_implies_Helper11Helper (G : Type*) [Magma G] (h : Equation345169 G) (eq10 : ∀ (x y z : G), (x ◇ (y ◇ z)) ◇ (y ◇ x) = x) (eq11 : ∀ (x y : G), x ◇ (y ◇ (x ◇ y)) = x ◇ x) :
∀ x y z : G, (x ◇ (y ◇ z)) ◇ ((y ◇ x) ◇ x) = (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq12 : ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ sK0)) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X3 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.2 in 10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1 in 10
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq28 (X0 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X2 := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).1.1.2 in 10
  have eq34 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).1.1.2 in 9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).1.2 in 9
  have eq49 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = X3 := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).1.1.2 in 10
  have eq70 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq18 eq28 -- superposition 28,18, 18 into 28, unify on (0).2 in 18 and (0).1.2 in 28
  have eq156 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq331 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq34 -- superposition 34,10, 10 into 34, unify on (0).2 in 10 and (0).1.2.2 in 34
  have eq335 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq11 eq34 -- superposition 34,11, 11 into 34, unify on (0).2 in 11 and (0).1.2.2 in 34
  have eq373 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq10 eq335 -- forward demodulation 335,10
  have eq394 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq70 eq331 -- superposition 331,70, 70 into 331, unify on (0).2 in 70 and (0).1.1 in 331
  have eq401 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) ◇ X1) := superpose eq331 eq9 -- superposition 9,331, 331 into 9, unify on (0).2 in 331 and (0).1.2 in 9
  have eq426 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) := superpose eq70 eq401 -- forward demodulation 401,70
  have eq427 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq426 eq156 -- backward demodulation 156,426
  have eq465 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) := superpose eq9 eq49 -- superposition 49,9, 9 into 49, unify on (0).2 in 9 and (0).1.2 in 49
  have eq519 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq465 eq39 -- backward demodulation 39,465
  have eq586 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ (X3 ◇ X0)) ◇ X3) := superpose eq10 eq519 -- superposition 519,10, 10 into 519, unify on (0).2 in 10 and (0).1.2 in 519
  have eq628 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq519 eq13 -- superposition 13,519, 519 into 13, unify on (0).2 in 519 and (0).1.2 in 13
  have eq667 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq427 -- superposition 427,10, 10 into 427, unify on (0).2 in 10 and (0).2.2.1 in 427
  have eq719  : ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ sK0)) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq667 eq12 -- backward demodulation 12,667
  have eq767 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq586 eq28 -- superposition 28,586, 586 into 28, unify on (0).2 in 586 and (0).1.1 in 28
  have eq773 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq586 eq394 -- superposition 394,586, 586 into 394, unify on (0).2 in 586 and (0).1.1 in 394
  have eq783 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq628 eq767 -- forward demodulation 767,628
  have eq794 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq773 eq373 -- backward demodulation 373,773
  have eq904  : ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ sK0)) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq794 eq719 -- backward demodulation 719,794
  have eq1018  : ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK0)) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := superpose eq794 eq904 -- forward demodulation 904,794
  have eq1019 : ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := superpose eq783 eq1018 -- forward demodulation 1018,783
  subsumption eq1019 eq794

theorem Equation345169_implies_Helper12 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, (x ◇ y) ◇ y = y ◇ (x ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq569 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq577 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq672 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq569 -- forward demodulation 569,177
  have eq677 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq577 -- forward demodulation 577,177
  have eq678 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq677 -- forward demodulation 677,108
  have eq679 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq678 -- forward demodulation 678,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq679 -- superposition 679,7, 7 into 679, unify on (0).2 in 7 and (0).1 in 679
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1117 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1153 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1168 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1153 -- forward demodulation 1153,182
  have eq1169 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1168 eq1117 -- backward demodulation 1117,1168
  have eq1183 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1169 -- forward demodulation 1169,127
  have eq1184 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1183 eq9 -- backward demodulation 9,1183
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).2.2 in 1184
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1183 eq1183 -- superposition 1183,1183, 1183 into 1183, unify on (0).2 in 1183 and (0).1.1 in 1183
  have eq1831 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1854 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1183 eq1831 -- forward demodulation 1831,1183
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1854 eq11 -- superposition 11,1854, 1854 into 11, unify on (0).2 in 1854 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2204 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq672 -- backward demodulation 672,2149
  have eq2364 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2376 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2500 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2204 -- forward demodulation 2204,2149
  have eq2745 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2364 -- forward demodulation 2364,2149
  have eq3441 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2745 -- superposition 2745,182, 182 into 2745, unify on (0).2 in 182 and (0).1.1 in 2745
  have eq3526 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3441 -- forward demodulation 3441,887
  have eq3549 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3526 eq2149 -- backward demodulation 2149,3526
  have eq3640 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3549 eq503 -- backward demodulation 503,3549
  have eq3667 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2376 eq3526 -- superposition 3526,2376, 2376 into 3526, unify on (0).2 in 2376 and (0).1 in 3526
  have eq3718 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq3526 eq8 -- superposition 8,3526, 3526 into 8, unify on (0).2 in 3526 and (0).1 in 8
  have eq4354 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3526 eq2500 -- superposition 2500,3526, 3526 into 2500, unify on (0).2 in 3526 and (0).1.1 in 2500
  have eq7405 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3667 eq2745 -- superposition 2745,3667, 3667 into 2745, unify on (0).2 in 3667 and (0).2.2 in 2745
  have eq10843 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3640 eq4354 -- superposition 4354,3640, 3640 into 4354, unify on (0).2 in 3640 and (0).1.1 in 4354
  have eq11066 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7405 eq10843 -- forward demodulation 10843,7405
  have eq25730 : (sK1 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq11066 eq3718 -- superposition 3718,11066, 11066 into 3718, unify on (0).2 in 11066 and (0).2 in 3718
  subsumption eq25730 rfl

theorem Equation345169_implies_Helper14 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, ((x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z))) ◇ (y ◇ y) = x ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.2.1 in 10
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11 -- superposition 11,7, 7 into 11, unify on (0).2 in 7 and (0).1.2.1 in 11
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X2 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq11 eq7 -- superposition 7,11, 11 into 7, unify on (0).2 in 11 and (0).1.1.2.1 in 7
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq255 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq182 eq12 -- superposition 12,182, 182 into 12, unify on (0).2 in 182 and (0).2.1.1 in 12
  have eq280 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq108 eq255 -- forward demodulation 255,108
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq530 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq127 eq127 -- superposition 127,127, 127 into 127, unify on (0).2 in 127 and (0).1.1.2.1 in 127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) ◇ X1) := superpose eq127 eq7 -- superposition 7,127, 127 into 7, unify on (0).2 in 127 and (0).1.2 in 7
  have eq551 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq127 eq14 -- superposition 14,127, 127 into 14, unify on (0).2 in 127 and (0).1.1.2.1 in 14
  have eq552 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq127 eq28 -- superposition 28,127, 127 into 28, unify on (0).2 in 127 and (0).1.2.1 in 28
  have eq569 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq577 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq578 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq177 eq530 -- forward demodulation 530,177
  have eq598 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq551 -- forward demodulation 551,177
  have eq600 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq598 eq33 -- backward demodulation 33,598
  have eq663 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq177 eq552 -- forward demodulation 552,177
  have eq664 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq108 eq663 -- forward demodulation 663,108
  have eq672 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq569 -- forward demodulation 569,177
  have eq677 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq577 -- forward demodulation 577,177
  have eq678 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq677 -- forward demodulation 677,108
  have eq679 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq678 -- forward demodulation 678,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq679 -- superposition 679,7, 7 into 679, unify on (0).2 in 7 and (0).1 in 679
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1117 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1153 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1168 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1153 -- forward demodulation 1153,182
  have eq1169 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1168 eq1117 -- backward demodulation 1117,1168
  have eq1183 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1169 -- forward demodulation 1169,127
  have eq1184 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1183 eq9 -- backward demodulation 9,1183
  have eq1187 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq1183 eq23 -- backward demodulation 23,1183
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).2.2 in 1184
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1183 eq1183 -- superposition 1183,1183, 1183 into 1183, unify on (0).2 in 1183 and (0).1.1 in 1183
  have eq1831 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1854 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1183 eq1831 -- forward demodulation 1831,1183
  have eq1855 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq1854 eq280 -- backward demodulation 280,1854
  have eq2068 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq1854 -- superposition 1854,7, 7 into 1854, unify on (0).2 in 7 and (0).1.2 in 1854
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1854 eq11 -- superposition 11,1854, 1854 into 11, unify on (0).2 in 1854 and (0).2.1.2.1 in 11
  have eq2137 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq108 eq2068 -- forward demodulation 2068,108
  have eq2138 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq2137 eq1855 -- backward demodulation 1855,2137
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2161 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq2149 eq127 -- backward demodulation 127,2149
  have eq2169 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) := superpose eq2149 eq547 -- backward demodulation 547,2149
  have eq2172 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2149 eq578 -- backward demodulation 578,2149
  have eq2173 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq2149 eq598 -- backward demodulation 598,2149
  have eq2175 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq2149 eq600 -- backward demodulation 600,2149
  have eq2200 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq664 -- backward demodulation 664,2149
  have eq2204 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq672 -- backward demodulation 672,2149
  have eq2225 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq1187 -- backward demodulation 1187,2149
  have eq2348 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2364 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2376 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2437 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq2149 eq2169 -- forward demodulation 2169,2149
  have eq2442 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) := superpose eq2149 eq2175 -- forward demodulation 2175,2149
  have eq2500 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2204 -- forward demodulation 2204,2149
  have eq2539 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq2225 -- forward demodulation 2225,2149
  have eq2716 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2348 -- forward demodulation 2348,2149
  have eq2745 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2364 -- forward demodulation 2364,2149
  have eq2840 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2150 eq2150 -- superposition 2150,2150, 2150 into 2150, unify on (0).2 in 2150 and (0).1.1 in 2150
  have eq3236 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq2200 eq2539 -- superposition 2539,2200, 2200 into 2539, unify on (0).2 in 2200 and (0).1.1.1 in 2539
  have eq3441 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2745 -- superposition 2745,182, 182 into 2745, unify on (0).2 in 182 and (0).1.1 in 2745
  have eq3526 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3441 -- forward demodulation 3441,887
  have eq3549 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3526 eq2149 -- backward demodulation 2149,3526
  have eq3550 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq3526 eq2173 -- backward demodulation 2173,3526
  have eq3640 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3549 eq503 -- backward demodulation 503,3549
  have eq3667 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2376 eq3526 -- superposition 3526,2376, 2376 into 3526, unify on (0).2 in 2376 and (0).1 in 3526
  have eq3684 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq3526 eq2150 -- superposition 2150,3526, 3526 into 2150, unify on (0).2 in 3526 and (0).1.1 in 2150
  have eq3702 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq3526 eq2716 -- superposition 2716,3526, 3526 into 2716, unify on (0).2 in 3526 and (0).1 in 2716
  have eq3703 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3526 eq2376 -- superposition 2376,3526, 3526 into 2376, unify on (0).2 in 3526 and (0).1.1 in 2376
  have eq3709 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3526 eq2150 -- superposition 2150,3526, 3526 into 2150, unify on (0).2 in 3526 and (0).1.2 in 2150
  have eq4354 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3526 eq2500 -- superposition 2500,3526, 3526 into 2500, unify on (0).2 in 3526 and (0).1.1 in 2500
  have eq4382 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq3526 eq2500 -- superposition 2500,3526, 3526 into 2500, unify on (0).2 in 3526 and (0).1 in 2500
  have eq5565 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq887 eq3236 -- superposition 3236,887, 887 into 3236, unify on (0).2 in 887 and (0).1.1.1 in 3236
  have eq6116 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq3640 eq3236 -- superposition 3236,3640, 3640 into 3236, unify on (0).2 in 3640 and (0).1.1 in 3236
  have eq7100 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3667 eq2745 -- superposition 2745,3667, 3667 into 2745, unify on (0).2 in 3667 and (0).2.2 in 2745
  have eq7378 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq2376 eq2442 -- superposition 2442,2376, 2376 into 2442, unify on (0).2 in 2376 and (0).2.2 in 2442
  have eq7644 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq3640 eq3684 -- superposition 3684,3640, 3640 into 3684, unify on (0).2 in 3640 and (0).1.2 in 3684
  have eq7772 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7100 eq7644 -- forward demodulation 7644,7100
  have eq8959 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq3703 eq2840 -- superposition 2840,3703, 3703 into 2840, unify on (0).2 in 3703 and (0).2.2 in 2840
  have eq9098 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq3526 eq8959 -- forward demodulation 8959,3526
  have eq9724 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3709 eq2716 -- superposition 2716,3709, 3709 into 2716, unify on (0).2 in 3709 and (0).2.1 in 2716
  have eq9852 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3526 eq9724 -- forward demodulation 9724,3526
  have eq10415 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3640 eq4354 -- superposition 4354,3640, 3640 into 4354, unify on (0).2 in 3640 and (0).1.1 in 4354
  have eq10631 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7100 eq10415 -- forward demodulation 10415,7100
  have eq10633 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq10631 eq8 -- backward demodulation 8,10631
  have eq10635 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3526 eq10633 -- forward demodulation 10633,3526
  have eq10786 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1183 eq4382 -- superposition 4382,1183, 1183 into 4382, unify on (0).2 in 1183 and (0).1.2 in 4382
  have eq10980 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq9852 eq10786 -- forward demodulation 10786,9852
  have eq18750 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1854 eq7100 -- superposition 7100,1854, 1854 into 7100, unify on (0).2 in 1854 and (0).2.1.2 in 7100
  have eq18815 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq7100 eq1183 -- superposition 1183,7100, 7100 into 1183, unify on (0).2 in 7100 and (0).1.1 in 1183
  have eq19016 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq2138 eq18750 -- forward demodulation 18750,2138
  have eq19017 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := superpose eq19016 eq10635 -- backward demodulation 10635,19016
  have eq19102 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq182 eq7772 -- superposition 7772,182, 182 into 7772, unify on (0).2 in 182 and (0).1.1 in 7772
  have eq19514 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7772 eq3550 -- superposition 3550,7772, 7772 into 3550, unify on (0).2 in 7772 and (0).1 in 3550
  have eq19638 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq5565 eq19514 -- forward demodulation 19514,5565
  have eq20406 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq3640 eq9098 -- superposition 9098,3640, 3640 into 9098, unify on (0).2 in 3640 and (0).2.2.2 in 9098
  have eq20694 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq2437 eq20406 -- forward demodulation 20406,2437
  have eq22587 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2161 eq10631 -- superposition 10631,2161, 2161 into 10631, unify on (0).2 in 2161 and (0).2.2 in 10631
  have eq23041 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq10631 eq3550 -- superposition 3550,10631, 10631 into 3550, unify on (0).2 in 10631 and (0).1 in 3550
  have eq23120 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2138 eq22587 -- forward demodulation 22587,2138
  have eq23192 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose eq2150 eq23041 -- forward demodulation 23041,2150
  have eq24159 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7772 eq10980 -- superposition 10980,7772, 7772 into 10980, unify on (0).2 in 7772 and (0).2 in 10980
  have eq30334 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq10631 eq19638 -- superposition 19638,10631, 10631 into 19638, unify on (0).2 in 10631 and (0).1.1 in 19638
  have eq30355 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq10980 eq19638 -- superposition 19638,10980, 10980 into 19638, unify on (0).2 in 10980 and (0).2 in 19638
  have eq30894 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq30334 eq18815 -- backward demodulation 18815,30334
  have eq37480 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7378 eq19102 -- superposition 19102,7378, 7378 into 19102, unify on (0).2 in 7378 and (0).2.2.1 in 19102
  have eq37887 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7378 eq10631 -- superposition 10631,7378, 7378 into 10631, unify on (0).2 in 7378 and (0).2.2 in 10631
  have eq37891 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7378 eq24159 -- superposition 24159,7378, 7378 into 24159, unify on (0).2 in 7378 and (0).2.2 in 24159
  have eq51988 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7378 eq30355 -- superposition 30355,7378, 7378 into 30355, unify on (0).2 in 7378 and (0).1.1 in 30355
  have eq59331 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq2172 eq7772 -- superposition 7772,2172, 2172 into 7772, unify on (0).2 in 2172 and (0).2.2 in 7772
  have eq59422 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq23120 eq59331 -- forward demodulation 59331,23120
  have eq59423 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq59422 eq51988 -- backward demodulation 51988,59422
  have eq59425 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq59423 eq37891 -- backward demodulation 37891,59423
  have eq59444 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq59425 eq37887 -- backward demodulation 37887,59425
  have eq79687 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq6116 eq7100 -- superposition 7100,6116, 6116 into 7100, unify on (0).2 in 6116 and (0).2.1.2 in 7100
  have eq79899 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq23192 eq79687 -- forward demodulation 79687,23192
  have eq79900 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq59444 eq79899 -- forward demodulation 79899,59444
  have eq81480 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) := superpose eq79900 eq7772 -- superposition 7772,79900, 79900 into 7772, unify on (0).2 in 79900 and (0).1.1 in 7772
  have eq211191 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq3702 eq9098 -- superposition 9098,3702, 3702 into 9098, unify on (0).2 in 3702 and (0).2.2.2 in 9098
  have eq211493 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq19638 eq211191 -- forward demodulation 211191,19638
  have eq493584 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq20694 eq7772 -- superposition 7772,20694, 20694 into 7772, unify on (0).2 in 20694 and (0).1.1 in 7772
  have eq738906 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq211493 eq3702 -- superposition 3702,211493, 211493 into 3702, unify on (0).2 in 211493 and (0).2.1 in 3702
  have eq1060629 : ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq81480 eq19017 -- superposition 19017,81480, 81480 into 19017, unify on (0).2 in 81480 and (0).2 in 19017
  have eq1061032 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq3526 eq1060629 -- forward demodulation 1060629,3526
  have eq1061033 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := superpose eq738906 eq1061032 -- forward demodulation 1061032,738906
  have eq6624370 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq493584 eq37480 -- superposition 37480,493584, 493584 into 37480, unify on (0).2 in 493584 and (0).2.2 in 37480
  have eq6628111 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X0) := superpose eq3549 eq6624370 -- superposition 6624370,3549, 3549 into 6624370, unify on (0).2 in 3549 and (0).2 in 6624370
  have eq6630642 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq3526 eq6628111 -- superposition 6628111,3526, 3526 into 6628111, unify on (0).2 in 3526 and (0).2 in 6628111
  have eq6787992 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq30894 eq1061033 -- superposition 1061033,30894, 30894 into 1061033, unify on (0).2 in 30894 and (0).2 in 1061033
  subsumption eq6787992 eq6630642

theorem Equation345169_implies_Helper15 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ ((y ◇ x) ◇ z)) = x ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8  : (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK2))) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq548 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq570 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq599 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq548 -- forward demodulation 548,177
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq599 -- forward demodulation 599,108
  have eq601 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq600 -- forward demodulation 600,503
  have eq679 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq570 -- forward demodulation 570,177
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq601 -- superposition 601,7, 7 into 601, unify on (0).2 in 7 and (0).1 in 601
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2202 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq679 -- backward demodulation 679,2149
  have eq2346 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2497 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2202 -- forward demodulation 2202,2149
  have eq2713 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2346 -- forward demodulation 2346,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq2837 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2150 eq2150 -- superposition 2150,2150, 2150 into 2150, unify on (0).2 in 2150 and (0).1.1 in 2150
  have eq3083 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq2837 eq2837 -- superposition 2837,2837, 2837 into 2837, unify on (0).2 in 2837 and (0).1 in 2837
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3546 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq2149 -- backward demodulation 2149,3523
  have eq3587 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))))) := superpose eq3523 eq3083 -- backward demodulation 3083,3523
  have eq3629 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK2))) := superpose eq3523 eq8 -- backward demodulation 8,3523
  have eq3638 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3546 eq503 -- backward demodulation 503,3546
  have eq3649 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := superpose eq3523 eq3629 -- forward demodulation 3629,3523
  have eq3666 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2374 eq3523 -- superposition 3523,2374, 2374 into 3523, unify on (0).2 in 2374 and (0).1 in 3523
  have eq3701 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3523 eq2150 -- superposition 2150,3523, 3523 into 2150, unify on (0).2 in 3523 and (0).1.2 in 2150
  have eq3707 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq3523 eq2713 -- superposition 2713,3523, 3523 into 2713, unify on (0).2 in 3523 and (0).1 in 2713
  have eq3708 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3523 eq2374 -- superposition 2374,3523, 3523 into 2374, unify on (0).2 in 3523 and (0).1.1 in 2374
  have eq4197 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1.1 in 2497
  have eq4224 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1 in 2497
  have eq6781 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3666 eq2742 -- superposition 2742,3666, 3666 into 2742, unify on (0).2 in 3666 and (0).2.2 in 2742
  have eq8602 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3701 eq2713 -- superposition 2713,3701, 3701 into 2713, unify on (0).2 in 3701 and (0).2.1 in 2713
  have eq8712 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3523 eq8602 -- forward demodulation 8602,3523
  have eq9940 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3638 eq4197 -- superposition 4197,3638, 3638 into 4197, unify on (0).2 in 3638 and (0).1.1 in 4197
  have eq10148 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq6781 eq9940 -- forward demodulation 9940,6781
  have eq10149 : (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq10148 eq3649 -- backward demodulation 3649,10148
  have eq10150 : (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3523 eq10149 -- forward demodulation 10149,3523
  have eq10295 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1184 eq4224 -- superposition 4224,1184, 1184 into 4224, unify on (0).2 in 1184 and (0).1.2 in 4224
  have eq10482 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq8712 eq10295 -- forward demodulation 10295,8712
  have eq11612 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2)) := superpose eq3708 eq3587 -- superposition 3587,3708, 3708 into 3587, unify on (0).2 in 3708 and (0).2.2 in 3587
  have eq11776 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq3523 eq11612 -- forward demodulation 11612,3523
  have eq325636 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11776 eq3707 -- superposition 3707,11776, 11776 into 3707, unify on (0).2 in 11776 and (0).2.1 in 3707
  have eq759257 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq325636 eq10150 -- superposition 10150,325636, 325636 into 10150, unify on (0).2 in 325636 and (0).1 in 10150
  subsumption eq759257 eq10482

theorem Equation345169_implies_Helper16 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ (z ◇ (x ◇ y))) = x ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq570 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq679 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq570 -- forward demodulation 570,177
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2202 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq679 -- backward demodulation 679,2149
  have eq2346 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2497 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2202 -- forward demodulation 2202,2149
  have eq2713 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2346 -- forward demodulation 2346,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq2837 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2150 eq2150 -- superposition 2150,2150, 2150 into 2150, unify on (0).2 in 2150 and (0).1.1 in 2150
  have eq3083 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq2837 eq2837 -- superposition 2837,2837, 2837 into 2837, unify on (0).2 in 2837 and (0).1 in 2837
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3546 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq2149 -- backward demodulation 2149,3523
  have eq3587 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))))) := superpose eq3523 eq3083 -- backward demodulation 3083,3523
  have eq3637 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3546 eq503 -- backward demodulation 503,3546
  have eq3664 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2374 eq3523 -- superposition 3523,2374, 2374 into 3523, unify on (0).2 in 2374 and (0).1 in 3523
  have eq3699 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3523 eq2150 -- superposition 2150,3523, 3523 into 2150, unify on (0).2 in 3523 and (0).1.2 in 2150
  have eq3704 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq3523 eq2713 -- superposition 2713,3523, 3523 into 2713, unify on (0).2 in 3523 and (0).1 in 2713
  have eq3705 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3523 eq2374 -- superposition 2374,3523, 3523 into 2374, unify on (0).2 in 3523 and (0).1.1 in 2374
  have eq4349 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1.1 in 2497
  have eq4377 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1 in 2497
  have eq7101 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3664 eq2742 -- superposition 2742,3664, 3664 into 2742, unify on (0).2 in 3664 and (0).2.2 in 2742
  have eq8962 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3699 eq2713 -- superposition 2713,3699, 3699 into 2713, unify on (0).2 in 3699 and (0).2.1 in 2713
  have eq9076 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3523 eq8962 -- forward demodulation 8962,3523
  have eq10409 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3637 eq4349 -- superposition 4349,3637, 3637 into 4349, unify on (0).2 in 3637 and (0).1.1 in 4349
  have eq10625 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7101 eq10409 -- forward demodulation 10409,7101
  have eq10626 : (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq10625 eq8 -- backward demodulation 8,10625
  have eq10627: (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3523 eq10626 -- forward demodulation 10626,3523
  have eq10776 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1184 eq4377 -- superposition 4377,1184, 1184 into 4377, unify on (0).2 in 1184 and (0).1.2 in 4377
  have eq10970 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq9076 eq10776 -- forward demodulation 10776,9076
  have eq11274 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2)) := superpose eq3705 eq3587 -- superposition 3587,3705, 3705 into 3587, unify on (0).2 in 3705 and (0).2.2 in 3587
  have eq11435 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq3523 eq11274 -- forward demodulation 11274,3523
  have eq325697 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11435 eq3704 -- superposition 3704,11435, 11435 into 3704, unify on (0).2 in 11435 and (0).2.1 in 3704
  have eq769282 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose eq325697 eq10627 -- superposition 10627,325697, 325697 into 10627, unify on (0).2 in 325697 and (0).1 in 10627
  subsumption eq769282 eq10970

theorem Equation345169_implies_Helper17 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ (y ◇ y) = x ◇ (x ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq570 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq598 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq547 -- forward demodulation 547,177
  have eq599 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq598 -- forward demodulation 598,108
  have eq600 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq599 -- forward demodulation 599,503
  have eq679 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq570 -- forward demodulation 570,177
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq600 -- superposition 600,7, 7 into 600, unify on (0).2 in 7 and (0).1 in 600
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1150 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1150 -- forward demodulation 1150,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1825 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1853 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1825 -- forward demodulation 1825,1184
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1853 eq11 -- superposition 11,1853, 1853 into 11, unify on (0).2 in 1853 and (0).2.1.2.1 in 11
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2202 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq679 -- backward demodulation 679,2149
  have eq2362 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2374 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2497 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2202 -- forward demodulation 2202,2149
  have eq2742 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2362 -- forward demodulation 2362,2149
  have eq3438 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2742 -- superposition 2742,182, 182 into 2742, unify on (0).2 in 182 and (0).1.1 in 2742
  have eq3523 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3438 -- forward demodulation 3438,887
  have eq3546 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3523 eq2149 -- backward demodulation 2149,3523
  have eq3637 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3546 eq503 -- backward demodulation 503,3546
  have eq3664 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2374 eq3523 -- superposition 3523,2374, 2374 into 3523, unify on (0).2 in 2374 and (0).1 in 3523
  have eq4349 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3523 eq2497 -- superposition 2497,3523, 3523 into 2497, unify on (0).2 in 3523 and (0).1.1 in 2497
  have eq7101 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3664 eq2742 -- superposition 2742,3664, 3664 into 2742, unify on (0).2 in 3664 and (0).2.2 in 2742
  have eq10409 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3637 eq4349 -- superposition 4349,3637, 3637 into 4349, unify on (0).2 in 3637 and (0).1.1 in 4349
  have eq10625 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7101 eq10409 -- forward demodulation 10409,7101
  have eq24650 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq10625 eq8 -- superposition 8,10625, 10625 into 8, unify on (0).2 in 10625 and (0).1 in 8
  have eq24957 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3523 eq24650 -- forward demodulation 24650,3523
  subsumption eq24957 rfl

theorem Equation345169_implies_Helper20 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, ((x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z))) ◇ (y ◇ y) = x ◇ (y ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.2.1 in 10
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11 -- superposition 11,7, 7 into 11, unify on (0).2 in 7 and (0).1.2.1 in 11
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X2 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq11 eq7 -- superposition 7,11, 11 into 7, unify on (0).2 in 11 and (0).1.1.2.1 in 7
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq255 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq182 eq12 -- superposition 12,182, 182 into 12, unify on (0).2 in 182 and (0).2.1.1 in 12
  have eq280 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq108 eq255 -- forward demodulation 255,108
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq530 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq127 eq127 -- superposition 127,127, 127 into 127, unify on (0).2 in 127 and (0).1.1.2.1 in 127
  have eq547 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) ◇ X1) := superpose eq127 eq7 -- superposition 7,127, 127 into 7, unify on (0).2 in 127 and (0).1.2 in 7
  have eq551 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq127 eq14 -- superposition 14,127, 127 into 14, unify on (0).2 in 127 and (0).1.1.2.1 in 14
  have eq552 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq127 eq28 -- superposition 28,127, 127 into 28, unify on (0).2 in 127 and (0).1.2.1 in 28
  have eq569 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq577 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq578 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq177 eq530 -- forward demodulation 530,177
  have eq598 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq551 -- forward demodulation 551,177
  have eq600 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq598 eq33 -- backward demodulation 33,598
  have eq663 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq177 eq552 -- forward demodulation 552,177
  have eq664 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq108 eq663 -- forward demodulation 663,108
  have eq672 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq569 -- forward demodulation 569,177
  have eq677 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq577 -- forward demodulation 577,177
  have eq678 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq677 -- forward demodulation 677,108
  have eq679 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq678 -- forward demodulation 678,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq679 -- superposition 679,7, 7 into 679, unify on (0).2 in 7 and (0).1 in 679
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1117 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1153 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1168 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1153 -- forward demodulation 1153,182
  have eq1169 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1168 eq1117 -- backward demodulation 1117,1168
  have eq1183 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1169 -- forward demodulation 1169,127
  have eq1184 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1183 eq9 -- backward demodulation 9,1183
  have eq1187 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq1183 eq23 -- backward demodulation 23,1183
  have eq1548 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).2.2 in 1184
  have eq1624 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1183 eq1183 -- superposition 1183,1183, 1183 into 1183, unify on (0).2 in 1183 and (0).1.1 in 1183
  have eq1831 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1624 eq127 -- superposition 127,1624, 1624 into 127, unify on (0).2 in 1624 and (0).1.1.2.1 in 127
  have eq1854 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1183 eq1831 -- forward demodulation 1831,1183
  have eq1855 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq1854 eq280 -- backward demodulation 280,1854
  have eq2068 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq1854 -- superposition 1854,7, 7 into 1854, unify on (0).2 in 7 and (0).1.2 in 1854
  have eq2075 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1854 eq11 -- superposition 11,1854, 1854 into 11, unify on (0).2 in 1854 and (0).2.1.2.1 in 11
  have eq2137 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq108 eq2068 -- forward demodulation 2068,108
  have eq2138 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq2137 eq1855 -- backward demodulation 1855,2137
  have eq2149 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2075 -- forward demodulation 2075,177
  have eq2150 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2149 eq7 -- backward demodulation 7,2149
  have eq2161 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq2149 eq127 -- backward demodulation 127,2149
  have eq2169 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) := superpose eq2149 eq547 -- backward demodulation 547,2149
  have eq2172 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2149 eq578 -- backward demodulation 578,2149
  have eq2173 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq2149 eq598 -- backward demodulation 598,2149
  have eq2175 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2))) := superpose eq2149 eq600 -- backward demodulation 600,2149
  have eq2200 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq664 -- backward demodulation 664,2149
  have eq2204 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq672 -- backward demodulation 672,2149
  have eq2225 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq1187 -- backward demodulation 1187,2149
  have eq2348 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2149 eq28 -- backward demodulation 28,2149
  have eq2364 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2149 eq1548 -- backward demodulation 1548,2149
  have eq2376 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2149 eq14 -- backward demodulation 14,2149
  have eq2437 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq2149 eq2169 -- forward demodulation 2169,2149
  have eq2442 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) := superpose eq2149 eq2175 -- forward demodulation 2175,2149
  have eq2500 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2149 eq2204 -- forward demodulation 2204,2149
  have eq2539 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2149 eq2225 -- forward demodulation 2225,2149
  have eq2716 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2149 eq2348 -- forward demodulation 2348,2149
  have eq2745 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2149 eq2364 -- forward demodulation 2364,2149
  have eq2840 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq2150 eq2150 -- superposition 2150,2150, 2150 into 2150, unify on (0).2 in 2150 and (0).1.1 in 2150
  have eq3236 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq2200 eq2539 -- superposition 2539,2200, 2200 into 2539, unify on (0).2 in 2200 and (0).1.1.1 in 2539
  have eq3441 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2745 -- superposition 2745,182, 182 into 2745, unify on (0).2 in 182 and (0).1.1 in 2745
  have eq3526 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3441 -- forward demodulation 3441,887
  have eq3549 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3526 eq2149 -- backward demodulation 2149,3526
  have eq3550 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq3526 eq2173 -- backward demodulation 2173,3526
  have eq3640 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3549 eq503 -- backward demodulation 503,3549
  have eq3667 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2376 eq3526 -- superposition 3526,2376, 2376 into 3526, unify on (0).2 in 2376 and (0).1 in 3526
  have eq3684 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq3526 eq2150 -- superposition 2150,3526, 3526 into 2150, unify on (0).2 in 3526 and (0).1.1 in 2150
  have eq3702 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq3526 eq2716 -- superposition 2716,3526, 3526 into 2716, unify on (0).2 in 3526 and (0).1 in 2716
  have eq3703 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3526 eq2376 -- superposition 2376,3526, 3526 into 2376, unify on (0).2 in 3526 and (0).1.1 in 2376
  have eq3709 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3526 eq2150 -- superposition 2150,3526, 3526 into 2150, unify on (0).2 in 3526 and (0).1.2 in 2150
  have eq4354 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq3526 eq2500 -- superposition 2500,3526, 3526 into 2500, unify on (0).2 in 3526 and (0).1.1 in 2500
  have eq4382 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq3526 eq2500 -- superposition 2500,3526, 3526 into 2500, unify on (0).2 in 3526 and (0).1 in 2500
  have eq5565 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq887 eq3236 -- superposition 3236,887, 887 into 3236, unify on (0).2 in 887 and (0).1.1.1 in 3236
  have eq6116 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq3640 eq3236 -- superposition 3236,3640, 3640 into 3236, unify on (0).2 in 3640 and (0).1.1 in 3236
  have eq7100 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3667 eq2745 -- superposition 2745,3667, 3667 into 2745, unify on (0).2 in 3667 and (0).2.2 in 2745
  have eq7378 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq2376 eq2442 -- superposition 2442,2376, 2376 into 2442, unify on (0).2 in 2376 and (0).2.2 in 2442
  have eq7644 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq3640 eq3684 -- superposition 3684,3640, 3640 into 3684, unify on (0).2 in 3640 and (0).1.2 in 3684
  have eq7772 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7100 eq7644 -- forward demodulation 7644,7100
  have eq8959 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq3703 eq2840 -- superposition 2840,3703, 3703 into 2840, unify on (0).2 in 3703 and (0).2.2 in 2840
  have eq9098 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq3526 eq8959 -- forward demodulation 8959,3526
  have eq9724 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3709 eq2716 -- superposition 2716,3709, 3709 into 2716, unify on (0).2 in 3709 and (0).2.1 in 2716
  have eq9852 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3526 eq9724 -- forward demodulation 9724,3526
  have eq10415 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq3640 eq4354 -- superposition 4354,3640, 3640 into 4354, unify on (0).2 in 3640 and (0).1.1 in 4354
  have eq10631 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7100 eq10415 -- forward demodulation 10415,7100
  have eq10633 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq10631 eq8 -- backward demodulation 8,10631
  have eq10635 : (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq3526 eq10633 -- forward demodulation 10633,3526
  have eq10786 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1183 eq4382 -- superposition 4382,1183, 1183 into 4382, unify on (0).2 in 1183 and (0).1.2 in 4382
  have eq10980 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq9852 eq10786 -- forward demodulation 10786,9852
  have eq18750 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1854 eq7100 -- superposition 7100,1854, 1854 into 7100, unify on (0).2 in 1854 and (0).2.1.2 in 7100
  have eq18815 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq7100 eq1183 -- superposition 1183,7100, 7100 into 1183, unify on (0).2 in 7100 and (0).1.1 in 1183
  have eq19016 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq2138 eq18750 -- forward demodulation 18750,2138
  have eq19017 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := superpose eq19016 eq10635 -- backward demodulation 10635,19016
  have eq19102 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq182 eq7772 -- superposition 7772,182, 182 into 7772, unify on (0).2 in 182 and (0).1.1 in 7772
  have eq19514 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7772 eq3550 -- superposition 3550,7772, 7772 into 3550, unify on (0).2 in 7772 and (0).1 in 3550
  have eq19638 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq5565 eq19514 -- forward demodulation 19514,5565
  have eq20406 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq3640 eq9098 -- superposition 9098,3640, 3640 into 9098, unify on (0).2 in 3640 and (0).2.2.2 in 9098
  have eq20694 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq2437 eq20406 -- forward demodulation 20406,2437
  have eq22587 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2161 eq10631 -- superposition 10631,2161, 2161 into 10631, unify on (0).2 in 2161 and (0).2.2 in 10631
  have eq23041 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq10631 eq3550 -- superposition 3550,10631, 10631 into 3550, unify on (0).2 in 10631 and (0).1 in 3550
  have eq23120 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq2138 eq22587 -- forward demodulation 22587,2138
  have eq23192 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose eq2150 eq23041 -- forward demodulation 23041,2150
  have eq24159 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7772 eq10980 -- superposition 10980,7772, 7772 into 10980, unify on (0).2 in 7772 and (0).2 in 10980
  have eq30334 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq10631 eq19638 -- superposition 19638,10631, 10631 into 19638, unify on (0).2 in 10631 and (0).1.1 in 19638
  have eq30355 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq10980 eq19638 -- superposition 19638,10980, 10980 into 19638, unify on (0).2 in 10980 and (0).2 in 19638
  have eq30894 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq30334 eq18815 -- backward demodulation 18815,30334
  have eq37480 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7378 eq19102 -- superposition 19102,7378, 7378 into 19102, unify on (0).2 in 7378 and (0).2.2.1 in 19102
  have eq37887 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7378 eq10631 -- superposition 10631,7378, 7378 into 10631, unify on (0).2 in 7378 and (0).2.2 in 10631
  have eq37891 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7378 eq24159 -- superposition 24159,7378, 7378 into 24159, unify on (0).2 in 7378 and (0).2.2 in 24159
  have eq51988 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7378 eq30355 -- superposition 30355,7378, 7378 into 30355, unify on (0).2 in 7378 and (0).1.1 in 30355
  have eq59331 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq2172 eq7772 -- superposition 7772,2172, 2172 into 7772, unify on (0).2 in 2172 and (0).2.2 in 7772
  have eq59422 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq23120 eq59331 -- forward demodulation 59331,23120
  have eq59423 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq59422 eq51988 -- backward demodulation 51988,59422
  have eq59425 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq59423 eq37891 -- backward demodulation 37891,59423
  have eq59444 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq59425 eq37887 -- backward demodulation 37887,59425
  have eq79687 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq6116 eq7100 -- superposition 7100,6116, 6116 into 7100, unify on (0).2 in 6116 and (0).2.1.2 in 7100
  have eq79899 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq23192 eq79687 -- forward demodulation 79687,23192
  have eq79900 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq59444 eq79899 -- forward demodulation 79899,59444
  have eq81480 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) := superpose eq79900 eq7772 -- superposition 7772,79900, 79900 into 7772, unify on (0).2 in 79900 and (0).1.1 in 7772
  have eq209950 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq3702 eq9098 -- superposition 9098,3702, 3702 into 9098, unify on (0).2 in 3702 and (0).2.2.2 in 9098
  have eq210252 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq19638 eq209950 -- forward demodulation 209950,19638
  have eq498330 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq20694 eq7772 -- superposition 7772,20694, 20694 into 7772, unify on (0).2 in 20694 and (0).1.1 in 7772
  have eq752457 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq210252 eq3702 -- superposition 3702,210252, 210252 into 3702, unify on (0).2 in 210252 and (0).2.1 in 3702
  have eq1074383  : ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq81480 eq19017 -- superposition 19017,81480, 81480 into 19017, unify on (0).2 in 81480 and (0).2 in 19017
  have eq1074794 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := superpose eq3526 eq1074383 -- forward demodulation 1074383,3526
  have eq1074795 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := superpose eq752457 eq1074794 -- forward demodulation 1074794,752457
  have eq6503853 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq498330 eq37480 -- superposition 37480,498330, 498330 into 37480, unify on (0).2 in 498330 and (0).2.2 in 37480
  have eq6507497 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X0) := superpose eq3549 eq6503853 -- superposition 6503853,3549, 3549 into 6503853, unify on (0).2 in 3549 and (0).2 in 6503853
  have eq6510028 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X0)) := superpose eq3526 eq6507497 -- superposition 6507497,3526, 3526 into 6507497, unify on (0).2 in 3526 and (0).2 in 6507497
  have eq6669826  : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq30894 eq1074795 -- superposition 1074795,30894, 30894 into 1074795, unify on (0).2 in 30894 and (0).2 in 1074795
  subsumption eq6669826 eq6510028

theorem Equation345169_implies_Helper21 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (((x ◇ y) ◇ (x ◇ y)) ◇ ((z ◇ ((x ◇ y) ◇ z)) ◇ (x ◇ y))) ◇ (x ◇ x) = (z ◇ ((x ◇ y) ◇ z)) ◇ (x ◇ x) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : ((((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) ≠ ((sK2 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.1.2.1 in 7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2.2 in 7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7 -- superposition 7,7, 7 into 7, unify on (0).2 in 7 and (0).1.2 in 7
  have eq14 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1.2 in 10
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq10 -- superposition 10,7, 7 into 10, unify on (0).2 in 7 and (0).1.1.1 in 10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11 -- superposition 11,7, 7 into 11, unify on (0).2 in 7 and (0).1.2.1 in 11
  have eq28 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).2.1.1 in 11
  have eq76 (X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = (((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2.2 in 9
  have eq106 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X1 ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.2 in 16
  have eq108 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq125 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq16 eq106 -- forward demodulation 106,16
  have eq127 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq125 -- backward demodulation 125,108
  have eq177 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.1 in 7
  have eq182 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq108 eq7 -- superposition 7,108, 108 into 7, unify on (0).2 in 108 and (0).1.2 in 7
  have eq373 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq177 eq28 -- superposition 28,177, 177 into 28, unify on (0).2 in 177 and (0).1.2.1 in 28
  have eq457 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq76 -- superposition 76,7, 7 into 76, unify on (0).2 in 7 and (0).2.2 in 76
  have eq501 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq108 eq457 -- forward demodulation 457,108
  have eq502 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq501 eq373 -- backward demodulation 373,501
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq127 eq502 -- forward demodulation 502,127
  have eq551 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq127 eq14 -- superposition 14,127, 127 into 14, unify on (0).2 in 127 and (0).1.1.2.1 in 14
  have eq552 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq127 eq28 -- superposition 28,127, 127 into 28, unify on (0).2 in 127 and (0).1.2.1 in 28
  have eq568 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X1) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) := superpose eq127 eq14 -- superposition 14,127, 127 into 14, unify on (0).2 in 127 and (0).1.2 in 14
  have eq569 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq127 eq16 -- superposition 16,127, 127 into 16, unify on (0).2 in 127 and (0).1.2.2.2.1 in 16
  have eq577 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq127 eq76 -- superposition 76,127, 127 into 76, unify on (0).2 in 127 and (0).2.2.2.2.1 in 76
  have eq598 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq551 -- forward demodulation 551,177
  have eq663 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq177 eq552 -- forward demodulation 552,177
  have eq664 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq108 eq663 -- forward demodulation 663,108
  have eq672 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X1)) = X2 := superpose eq177 eq569 -- forward demodulation 569,177
  have eq677 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq177 eq577 -- forward demodulation 577,177
  have eq678 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq108 eq677 -- forward demodulation 677,108
  have eq679 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq503 eq678 -- forward demodulation 678,503
  have eq823 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq679 -- superposition 679,7, 7 into 679, unify on (0).2 in 7 and (0).1 in 679
  have eq887 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq108 eq823 -- forward demodulation 823,108
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq887 eq28 -- superposition 28,887, 887 into 28, unify on (0).2 in 887 and (0).1.2.1 in 28
  have eq1154 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq887 eq127 -- superposition 127,887, 887 into 127, unify on (0).2 in 887 and (0).1.1.2.1 in 127
  have eq1169 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq182 eq1154 -- forward demodulation 1154,182
  have eq1170 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1169 eq1118 -- backward demodulation 1118,1169
  have eq1184 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq127 eq1170 -- forward demodulation 1170,127
  have eq1185 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq1184 eq9 -- backward demodulation 9,1184
  have eq1188 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq1184 eq23 -- backward demodulation 23,1184
  have eq1549 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1))) := superpose eq1185 eq1185 -- superposition 1185,1185, 1185 into 1185, unify on (0).2 in 1185 and (0).2.2 in 1185
  have eq1625 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1184 eq1184 -- superposition 1184,1184, 1184 into 1184, unify on (0).2 in 1184 and (0).1.1 in 1184
  have eq1832 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq1625 eq127 -- superposition 127,1625, 1625 into 127, unify on (0).2 in 1625 and (0).1.1.2.1 in 127
  have eq1855 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1184 eq1832 -- forward demodulation 1832,1184
  have eq2079 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq1855 eq11 -- superposition 11,1855, 1855 into 11, unify on (0).2 in 1855 and (0).2.1.2.1 in 11
  have eq2153 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq177 eq2079 -- forward demodulation 2079,177
  have eq2154 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2153 eq7 -- backward demodulation 7,2153
  have eq2175 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X1 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) := superpose eq2153 eq568 -- backward demodulation 568,2153
  have eq2177 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq2153 eq598 -- backward demodulation 598,2153
  have eq2204 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2153 eq664 -- backward demodulation 664,2153
  have eq2208 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X2 := superpose eq2153 eq672 -- backward demodulation 672,2153
  have eq2229 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) = X1 := superpose eq2153 eq1188 -- backward demodulation 1188,2153
  have eq2352 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X4) := superpose eq2153 eq28 -- backward demodulation 28,2153
  have eq2368 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq2153 eq1549 -- backward demodulation 1549,2153
  have eq2380 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq2153 eq14 -- backward demodulation 14,2153
  have eq2443 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq2153 eq2175 -- forward demodulation 2175,2153
  have eq2501 : ((sK2 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := superpose eq2204 eq8 -- backward demodulation 8,2204
  have eq2502 : sK0 ≠ ((sK2 ◇ ((sK0 ◇ sK1) ◇ sK2)) ◇ (sK0 ◇ sK0)) := superpose eq1855 eq2501 -- forward demodulation 2501,1855
  have eq2506 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq2153 eq2208 -- forward demodulation 2208,2153
  have eq2545 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq2153 eq2229 -- forward demodulation 2229,2153
  have eq2722 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X3 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) := superpose eq2153 eq2352 -- forward demodulation 2352,2153
  have eq2751 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2153 eq2368 -- forward demodulation 2368,2153
  have eq3275 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq2204 eq2545 -- superposition 2545,2204, 2204 into 2545, unify on (0).2 in 2204 and (0).1.1.1 in 2545
  have eq3484 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq182 eq2751 -- superposition 2751,182, 182 into 2751, unify on (0).2 in 182 and (0).1.1 in 2751
  have eq3509 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := superpose eq1184 eq2751 -- superposition 2751,1184, 1184 into 2751, unify on (0).2 in 1184 and (0).1 in 2751
  have eq3571 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq887 eq3484 -- forward demodulation 3484,887
  have eq3593 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3571 eq2153 -- backward demodulation 2153,3571
  have eq3594 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq3571 eq2177 -- backward demodulation 2177,3571
  have eq3675 : sK0 ≠ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := superpose eq3571 eq2502 -- backward demodulation 2502,3571
  have eq3684 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq3593 eq503 -- backward demodulation 503,3593
  have eq3711 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq2380 eq3571 -- superposition 3571,2380, 2380 into 3571, unify on (0).2 in 2380 and (0).1 in 3571
  have eq3731 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq3571 eq2154 -- superposition 2154,3571, 3571 into 2154, unify on (0).2 in 3571 and (0).1.1 in 2154
  have eq3750 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq3571 eq2380 -- superposition 2380,3571, 3571 into 2380, unify on (0).2 in 3571 and (0).1.1 in 2380
  have eq3756 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq3571 eq2154 -- superposition 2154,3571, 3571 into 2154, unify on (0).2 in 3571 and (0).1.2 in 2154
  have eq4080 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq3571 eq2506 -- superposition 2506,3571, 3571 into 2506, unify on (0).2 in 3571 and (0).1 in 2506
  have eq5074 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq887 eq3275 -- superposition 3275,887, 887 into 3275, unify on (0).2 in 887 and (0).1.1.1 in 3275
  have eq5563 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq3571 eq3684 -- superposition 3684,3571, 3571 into 3684, unify on (0).2 in 3571 and (0).1 in 3684
  have eq6476 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3711 eq2751 -- superposition 2751,3711, 3711 into 2751, unify on (0).2 in 3711 and (0).2.2 in 2751
  have eq7006 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq3684 eq3731 -- superposition 3731,3684, 3684 into 3731, unify on (0).2 in 3684 and (0).1.2 in 3731
  have eq7123 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq6476 eq7006 -- forward demodulation 7006,6476
  have eq8880 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3756 eq2722 -- superposition 2722,3756, 3756 into 2722, unify on (0).2 in 3756 and (0).2.1 in 2722
  have eq8998 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq3571 eq8880 -- forward demodulation 8880,3571
  have eq10346 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1184 eq4080 -- superposition 4080,1184, 1184 into 4080, unify on (0).2 in 1184 and (0).1.2 in 4080
  have eq10533 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq8998 eq10346 -- forward demodulation 10346,8998
  have eq14486 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq3509 eq3750 -- superposition 3750,3509, 3509 into 3750, unify on (0).2 in 3509 and (0).1.1 in 3750
  have eq14614 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq8998 eq14486 -- forward demodulation 14486,8998
  have eq18170 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) := superpose eq2751 eq6476 -- superposition 6476,2751, 2751 into 6476, unify on (0).2 in 2751 and (0).2.1.2 in 6476
  have eq18423 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X0) := superpose eq3571 eq18170 -- forward demodulation 18170,3571
  have eq18424 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) := superpose eq7123 eq18423 -- forward demodulation 18423,7123
  have eq19565 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7123 eq3594 -- superposition 3594,7123, 7123 into 3594, unify on (0).2 in 7123 and (0).1 in 3594
  have eq19688 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq5074 eq19565 -- forward demodulation 19565,5074
  have eq24305 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7123 eq10533 -- superposition 10533,7123, 7123 into 10533, unify on (0).2 in 7123 and (0).2 in 10533
  have eq26056 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14614 eq3594 -- superposition 3594,14614, 14614 into 3594, unify on (0).2 in 14614 and (0).1 in 3594
  have eq26433 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq3731 eq26056 -- forward demodulation 26056,3731
  have eq30310 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq10533 eq19688 -- superposition 19688,10533, 10533 into 19688, unify on (0).2 in 10533 and (0).2 in 19688
  have eq36378 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq24305 eq3594 -- superposition 3594,24305, 24305 into 3594, unify on (0).2 in 24305 and (0).1 in 3594
  have eq36772 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq5563 eq36378 -- forward demodulation 36378,5563
  have eq423382 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X1) := superpose eq182 eq18424 -- superposition 18424,182, 182 into 18424, unify on (0).2 in 182 and (0).2.1.1 in 18424
  have eq1387900 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) := superpose eq26433 eq423382 -- superposition 423382,26433, 26433 into 423382, unify on (0).2 in 26433 and (0).2.1.2.1 in 423382
  have eq1388435 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) := superpose eq36772 eq1387900 -- forward demodulation 1387900,36772
  have eq2208261 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ X0) := superpose eq2443 eq1388435 -- superposition 1388435,2443, 2443 into 1388435, unify on (0).2 in 2443 and (0).2 in 1388435
  have eq3035012 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq182 eq2208261 -- superposition 2208261,182, 182 into 2208261, unify on (0).2 in 182 and (0).1 in 2208261
  have eq3045672 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq5074 eq3035012 -- superposition 3035012,5074, 5074 into 3035012, unify on (0).2 in 5074 and (0).1.1.2 in 3035012
  have eq3047074 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := superpose eq30310 eq3045672 -- forward demodulation 3045672,30310
  have eq3076381 : sK0 ≠ sK0 := superpose eq3047074 eq3675 -- superposition 3675,3047074, 3047074 into 3675, unify on (0).2 in 3047074 and (0).2 in 3675
  subsumption eq3076381 rfl

theorem Equation345169_implies_Helper24Helper (G : Type*) [Magma G] (_ : Equation345169 G) (eq10 : ∀ (x y z : G), x = (x ◇ (y ◇ z)) ◇ (x ◇ z)) (eq11 : ∀ (y x z : G), y = (x ◇ ((y ◇ z) ◇ x)) ◇ (y ◇ y)) :
∀ x y z : G, x ◇ ((y ◇ ((x ◇ z) ◇ y)) ◇ x) = y ◇ ((x ◇ z) ◇ y) := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq12 : (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)) ≠ (sK0 ◇ ((sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)) ◇ sK0)) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq10 eq10 -- superposition 10,10, 10 into 10, unify on (0).2 in 10 and (0).1.1.2 in 10
  have eq18 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq11 -- superposition 11,10, 10 into 11, unify on (0).2 in 10 and (0).1.1.2 in 11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).1.1 in 10
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq99 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).1.1 in 10
  have eq110 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq31 eq99 -- forward demodulation 99,31
  have eq239 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq11 eq110 -- superposition 110,11, 11 into 110, unify on (0).2 in 11 and (0).1.1 in 110
  have eq272 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq239 eq20 -- backward demodulation 20,239
  have eq274 : (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK2) ◇ sK1)))) := superpose eq239 eq12 -- backward demodulation 12,239
  subsumption eq274 eq272
