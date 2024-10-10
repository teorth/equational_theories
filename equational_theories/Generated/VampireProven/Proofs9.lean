import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

@[equational_result]
theorem Equation3566_implies_Equation3803 (G : Type*) [Magma G] (h : Equation3566 G) : Equation3803 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq16 (X2 X3 X4 : G) : (X3 ◇ X4) = ((X2 ◇ X3) ◇ X4) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.1 in 13
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- backward demodulation 9,16
  have eq35 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq35 eq23


@[equational_result]
theorem Equation3569_implies_Equation3957 (G : Type*) [Magma G] (h : Equation3569 G) : Equation3957 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2))) = (((X2 ◇ X0) ◇ X3) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.1.1 in 12
  have eq19 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2 in 9
  have eq20 (X1 X2 X3 X4 : G) : (X4 ◇ X2) = (X2 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.2.1 in 9
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.1.1.2 in 12
  have eq45 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.2.2 in 19
  have eq50 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).2.2 in 19
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq83 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := superpose eq11 eq20 -- superposition 20,11, 11 into 20, unify on (0).2 in 11 and (0).2.2 in 20
  have eq86 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X3))) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).2.2 in 20
  have eq89 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3))) = (((X3 ◇ X0) ◇ X4) ◇ X3) := superpose eq20 eq12 -- superposition 12,20, 20 into 12, unify on (0).2 in 20 and (0).1.1.1 in 12
  have eq90 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq20 eq19 -- superposition 19,20, 20 into 19, unify on (0).2 in 20 and (0).2.2 in 19
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq19 eq45 -- superposition 45,19, 19 into 45, unify on (0).2 in 19 and (0).2.2 in 45
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq45 eq19 -- superposition 19,45, 45 into 19, unify on (0).2 in 45 and (0).2.2 in 19
  have eq122 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.1.1 in 12
  have eq126 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) = (((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.2.1 in 11
  have eq127 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.1.1.2 in 12
  have eq131 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X1) ◇ X0)) = (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.2 in 11
  have eq133 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.2 in 9
  have eq136 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq50 eq112 -- forward demodulation 112,50
  have eq141 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq118 eq90 -- backward demodulation 90,118
  have eq143 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq118 eq122 -- forward demodulation 122,118
  have eq147 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq118 eq126 -- forward demodulation 126,118
  have eq148 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq118 eq127 -- forward demodulation 127,118
  have eq151 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) := superpose eq118 eq131 -- forward demodulation 131,118
  have eq153 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq118 eq133 -- forward demodulation 133,118
  have eq164 (X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) = (((X2 ◇ X3) ◇ X4) ◇ X2) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2.2 in 15
  have eq170 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).1.2 in 15
  have eq175 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = (X4 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))))) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq209 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X3))) ◇ X0) = (((X0 ◇ X1) ◇ X3) ◇ X0) := superpose eq164 eq86 -- backward demodulation 86,164
  have eq212 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq164 eq83 -- backward demodulation 83,164
  have eq216 (X0 X2 : G) : (X0 ◇ X2) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq118 eq170 -- forward demodulation 170,118
  have eq222 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = ((X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4) := superpose eq9 eq175 -- forward demodulation 175,9
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq9 eq118 -- superposition 118,9, 9 into 118, unify on (0).2 in 9 and (0).2.2 in 118
  have eq227 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq118 eq118 -- superposition 118,118, 118 into 118, unify on (0).2 in 118 and (0).2.2 in 118
  have eq229 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = (((X2 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq118 -- superposition 118,11, 11 into 118, unify on (0).2 in 11 and (0).2.2 in 118
  have eq230 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq19 eq118 -- superposition 118,19, 19 into 118, unify on (0).2 in 19 and (0).2 in 118
  have eq251 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) := superpose eq118 eq12 -- superposition 12,118, 118 into 12, unify on (0).2 in 118 and (0).1.1 in 12
  have eq253 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ X1)) := superpose eq223 eq153 -- backward demodulation 153,223
  have eq257 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = ((X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) ◇ X0) := superpose eq253 eq209 -- backward demodulation 209,253
  have eq258 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq253 eq12 -- backward demodulation 12,253
  have eq267 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq253 eq52 -- backward demodulation 52,253
  have eq274 (X0 X1 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq253 eq89 -- backward demodulation 89,253
  have eq282 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq253 eq141 -- backward demodulation 141,253
  have eq296 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) := superpose eq253 eq257 -- forward demodulation 257,253
  have eq298 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = (X3 ◇ (X4 ◇ X3)) := superpose eq253 eq274 -- forward demodulation 274,253
  have eq313 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) := superpose eq298 eq296 -- backward demodulation 296,298
  have eq317 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq298 eq212 -- backward demodulation 212,298
  have eq347 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq230 eq267 -- backward demodulation 267,230
  have eq350 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq347 eq50 -- backward demodulation 50,347
  have eq351 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq347 eq136 -- backward demodulation 136,347
  have eq352 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq347 eq216 -- backward demodulation 216,347
  have eq353 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq347 eq282 -- backward demodulation 282,347
  have eq360 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq351 eq353 -- forward demodulation 353,351
  have eq375 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq223 eq251 -- forward demodulation 251,223
  have eq376 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = ((X3 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq9 eq375 -- forward demodulation 375,9
  have eq377 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = (X2 ◇ X2) := superpose eq360 eq376 -- forward demodulation 376,360
  have eq379 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq377 eq317 -- backward demodulation 317,377
  have eq382 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5)) ◇ X4) = (X4 ◇ X4) := superpose eq377 eq222 -- backward demodulation 222,377
  have eq383 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ X1))) = ((X1 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq352 eq379 -- forward demodulation 379,352
  have eq384 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq383 eq229 -- backward demodulation 229,383
  have eq389 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) := superpose eq384 eq151 -- backward demodulation 151,384
  have eq400 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq118 eq258 -- superposition 258,118, 118 into 258, unify on (0).2 in 118 and (0).1.1.1.2 in 258
  have eq401 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq11 eq258 -- superposition 258,11, 11 into 258, unify on (0).2 in 11 and (0).1.1.1.2 in 258
  have eq419 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq383 eq400 -- forward demodulation 400,383
  have eq420 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq419 eq148 -- backward demodulation 148,419
  have eq423 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq420 eq143 -- backward demodulation 143,420
  have eq424 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) = ((X3 ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq383 eq401 -- forward demodulation 401,383
  have eq425 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) = ((X3 ◇ X5) ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq424 eq37 -- backward demodulation 37,424
  have eq498 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq11 eq352 -- superposition 352,11, 11 into 352, unify on (0).2 in 11 and (0).2.1 in 352
  have eq523 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq227 eq498 -- forward demodulation 498,227
  have eq524 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq350 eq523 -- forward demodulation 523,350
  have eq525 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq352 eq524 -- forward demodulation 524,352
  have eq526 (X0 X3 : G) : (X3 ◇ X0) = (X0 ◇ (X3 ◇ X0)) := superpose eq525 eq313 -- backward demodulation 313,525
  have eq557 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq526 eq227 -- backward demodulation 227,526
  have eq584 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq526 eq525 -- backward demodulation 525,526
  have eq593 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq557 eq423 -- backward demodulation 423,557
  have eq599 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X0)) = (((X3 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq593 eq389 -- backward demodulation 389,593
  have eq603 (X0 X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq593 eq425 -- backward demodulation 425,593
  have eq616 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq584 eq147 -- backward demodulation 147,584
  have eq630 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X4) = (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X5)) ◇ X4) := superpose eq584 eq382 -- backward demodulation 382,584
  have eq645 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq584 eq599 -- backward demodulation 599,584
  have eq648 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq584 eq603 -- backward demodulation 603,584
  have eq663 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq584 eq616 -- forward demodulation 616,584
  have eq664 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq584 eq663 -- forward demodulation 663,584
  have eq665 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X2)) := superpose eq557 eq664 -- forward demodulation 664,557
  have eq666 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := superpose eq118 eq665 -- forward demodulation 665,118
  have eq670 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq666 eq593 -- backward demodulation 593,666
  have eq672 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK2) ◇ sK0) := superpose eq666 eq10 -- backward demodulation 10,666
  have eq695 (X3 X4 X5 : G) : (X4 ◇ X4) = (((X4 ◇ X3) ◇ X5) ◇ X4) := superpose eq666 eq630 -- forward demodulation 630,666
  have eq696 (X3 X4 X5 : G) : (X4 ◇ X4) = ((X3 ◇ X5) ◇ X4) := superpose eq584 eq695 -- forward demodulation 695,584
  have eq697 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq696 eq672 -- backward demodulation 672,696
  have eq708 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq666 eq645 -- forward demodulation 645,666
  have eq709 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := superpose eq670 eq708 -- forward demodulation 708,670
  have eq710 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (((X2 ◇ X1) ◇ X3) ◇ (X5 ◇ (X1 ◇ X2))) := superpose eq666 eq648 -- forward demodulation 648,666
  have eq711 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = ((X1 ◇ X2) ◇ X5) := superpose eq709 eq710 -- forward demodulation 710,709
  have eq712 (X1 X2 X3 X5 : G) : (X5 ◇ ((X2 ◇ X1) ◇ X3)) = (X2 ◇ X5) := superpose eq584 eq711 -- forward demodulation 711,584
  have eq713 (X1 X2 X3 X5 : G) : (X2 ◇ X5) = (X5 ◇ (X1 ◇ X3)) := superpose eq584 eq712 -- forward demodulation 712,584
  have eq800 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq118 eq713 -- superposition 713,118, 118 into 713, unify on (0).2 in 118 and (0).2 in 713
  have eq853 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X4 ◇ (X1 ◇ X2)) := superpose eq713 eq800 -- superposition 800,713, 713 into 800, unify on (0).2 in 713 and (0).1 in 800
  have eq888 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ sK1) := superpose eq800 eq697 -- superposition 697,800, 800 into 697, unify on (0).2 in 800 and (0).1 in 697
  have eq941 (X1 X2 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ (X1 ◇ X2)) := superpose eq713 eq888 -- superposition 888,713, 713 into 888, unify on (0).2 in 713 and (0).2 in 888
  subsumption eq941 eq853


@[equational_result]
theorem Equation3573_implies_Equation43 (G : Type*) [Magma G] (h : Equation3573 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X3 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X3) := superpose eq9 eq26 -- forward demodulation 26,9
  have eq85 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq9 eq45 -- superposition 45,9, 9 into 45, unify on (0).2 in 9 and (0).1 in 45
  have eq98 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X1)) = (X3 ◇ X1) := superpose eq9 eq85 -- forward demodulation 85,9
  have eq352 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X2) := superpose eq9 eq98 -- superposition 98,9, 9 into 98, unify on (0).2 in 9 and (0).1 in 98
  have eq582 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq352 eq10 -- superposition 10,352, 352 into 10, unify on (0).2 in 352 and (0).2 in 10
  subsumption eq582 rfl


@[equational_result]
theorem Equation3577_implies_Equation3344 (G : Type*) [Magma G] (h : Equation3577 G) : Equation3344 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = (X5 ◇ (X4 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq25 (X0 X3 X4 X5 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (((X4 ◇ X5) ◇ X0) ◇ X6) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq45 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = (((X4 ◇ X5) ◇ X3) ◇ X0) := superpose eq9 eq25 -- superposition 25,9, 9 into 25, unify on (0).2 in 9 and (0).1 in 25
  have eq87 (X0 X3 X6 : G) : (X6 ◇ (X3 ◇ X0)) = (X0 ◇ X6) := superpose eq45 eq25 -- backward demodulation 25,45
  have eq101 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq87 eq10 -- backward demodulation 10,87
  subsumption eq101 eq87


@[equational_result]
theorem Equation3583_implies_Equation343 (G : Type*) [Magma G] (h : Equation3583 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3583_implies_Equation375 (G : Type*) [Magma G] (h : Equation3583 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation3583_implies_Equation3989 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3989 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3583_implies_Equation4529 (G : Type*) [Magma G] (h : Equation3583 G) : Equation4529 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK1 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3587_implies_Equation343 (G : Type*) [Magma G] (h : Equation3587 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3587_implies_Equation378 (G : Type*) [Magma G] (h : Equation3587 G) : Equation378 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3587_implies_Equation3993 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3993 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3587_implies_Equation4533 (G : Type*) [Magma G] (h : Equation3587 G) : Equation4533 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK1 ◇ sK2) ≠ ((sK1 ◇ sK2) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3591_implies_Equation3794 (G : Type*) [Magma G] (h : Equation3591 G) : Equation3794 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X2) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK1)) := mod_symm nh
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
  have eq907 : (sK0 ◇ sK1) ≠ (sK2 ◇ ((sK2 ◇ sK0) ◇ sK1)) := superpose eq172 eq10 -- superposition 10,172, 172 into 10, unify on (0).2 in 172 and (0).2 in 10
  have eq946 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := superpose eq697 eq907 -- forward demodulation 907,697
  subsumption eq946 eq354


@[equational_result]
theorem Equation3600_implies_Equation343 (G : Type*) [Magma G] (h : Equation3600 G) : Equation343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq21 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq21 rfl


@[equational_result]
theorem Equation3600_implies_Equation385 (G : Type*) [Magma G] (h : Equation3600 G) : Equation385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq25 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation3600_implies_Equation4006 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4006 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation3600_implies_Equation4546 (G : Type*) [Magma G] (h : Equation3600 G) : Equation4546 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X1 ◇ X0)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK2 ◇ sK1) ◇ sK2) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq26 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq26 rfl


@[equational_result]
theorem Equation362_implies_Equation4068 (G : Type*) [Magma G] (h : Equation362 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq30 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ X0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq35 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ X0) ◇ X0) ◇ sK0) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2.1 in 30
  have eq41 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq9 eq35 -- forward demodulation 35,9
  subsumption eq41 eq9


@[equational_result]
theorem Equation3634_implies_Equation4564 (G : Type*) [Magma G] (h : Equation3634 G) : Equation4564 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ ((X3 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK3 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq14 (X3 X4 X5 : G) : (X3 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK1 ◇ sK2) ≠ ((sK3 ◇ sK1) ◇ sK2) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X2 ◇ X3) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq27 : (sK1 ◇ sK2) ≠ (sK1 ◇ sK2) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).2 in 15
  subsumption eq27 rfl


@[equational_result]
theorem Equation3671_implies_Equation3662 (G : Type*) [Magma G] (h : Equation3671 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq63 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).2.1 in 16
  have eq93 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq9 eq63 -- forward demodulation 63,9
  have eq115 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation3676_implies_Equation3705 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3705 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.2 in 9
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq20 -- superposition 20,9, 9 into 20, unify on (0).2 in 9 and (0).2.1 in 20
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq20 eq11 -- superposition 11,20, 20 into 11, unify on (0).2 in 20 and (0).2.2 in 11
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq30 -- superposition 30,9, 9 into 30, unify on (0).2 in 9 and (0).1 in 30
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq36 eq123 -- forward demodulation 123,36
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq147 eq43 -- backward demodulation 43,147
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq148 eq20 -- backward demodulation 20,148
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq149 eq11 -- backward demodulation 11,149
  have eq186 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq165 eq23 -- backward demodulation 23,165
  have eq191 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq186 eq77 -- backward demodulation 77,186
  have eq192 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq191 eq12 -- backward demodulation 12,191
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq192 eq149 -- superposition 149,192, 192 into 149, unify on (0).2 in 192 and (0).2 in 149
  have eq283 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq241 eq13 -- superposition 13,241, 241 into 13, unify on (0).2 in 241 and (0).2 in 13
  subsumption eq283 eq241


@[equational_result]
theorem Equation3679_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3701 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X0) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq137 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X0 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq464 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq137 -- superposition 137,14, 14 into 137, unify on (0).2 in 14 and (0).2 in 137
  subsumption eq464 eq29


@[equational_result]
theorem Equation3681_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3681 G) : Equation3707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = ((X3 ◇ X0) ◇ (X4 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq63 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq133 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X5) = (((X2 ◇ X0) ◇ (X5 ◇ X5)) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).2.2 in 12
  have eq149 (X0 X1 X2 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq16 eq121 -- superposition 121,16, 16 into 121, unify on (0).2 in 16 and (0).2.2 in 121
  have eq169 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X5 ◇ X4))) := superpose eq16 eq15 -- superposition 15,16, 16 into 15, unify on (0).2 in 16 and (0).2.1 in 15
  have eq243 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq133 eq169 -- forward demodulation 169,133
  have eq247 (X0 X3 X4 : G) : (X4 ◇ X4) = ((X0 ◇ X4) ◇ (X3 ◇ X3)) := superpose eq243 eq63 -- backward demodulation 63,243
  have eq251 (X0 X3 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X3 ◇ X3)) := superpose eq243 eq149 -- backward demodulation 149,243
  have eq445 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq247 eq14 -- superposition 14,247, 247 into 14, unify on (0).2 in 247 and (0).2 in 14
  have eq766 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq14 eq251 -- superposition 251,14, 14 into 251, unify on (0).2 in 14 and (0).2 in 251
  subsumption eq766 eq445


@[equational_result]
theorem Equation3683_implies_Equation3697 (G : Type*) [Magma G] (h : Equation3683 G) : Equation3697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK3)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((X4 ◇ X0) ◇ (X5 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq29 (X1 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X4 ◇ X5)) = (X3 ◇ X3) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq109 (X0 X3 X4 X5 X6 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X6)) = (X3 ◇ X3) := superpose eq29 eq11 -- superposition 11,29, 29 into 11, unify on (0).2 in 29 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ sK2) ◇ (X1 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq109


@[equational_result]
theorem Equation3695_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ X4) ◇ (X0 ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq121 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X0)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq374 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq13 eq16 -- superposition 16,13, 13 into 16, unify on (0).2 in 13 and (0).2 in 16
  have eq832 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq374 eq121 -- superposition 121,374, 374 into 121, unify on (0).2 in 374 and (0).2 in 121
  subsumption eq832 eq374


@[equational_result]
theorem Equation3696_implies_Equation3708 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3708 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq139 (X0 X1 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X1)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  have eq398 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq16 eq139 -- superposition 139,16, 16 into 139, unify on (0).2 in 16 and (0).2 in 139
  subsumption eq398 eq31


@[equational_result]
theorem Equation3697_implies_Equation3710 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK4)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X4 ◇ X5) ◇ (X0 ◇ X6)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq108 (X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X2 ◇ X6)) = (X3 ◇ X3) := superpose eq31 eq11 -- superposition 11,31, 31 into 11, unify on (0).2 in 31 and (0).1 in 11
  have eq137 (X0 X1 X2 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X1) ◇ (sK3 ◇ X2)) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq137 eq108


@[equational_result]
theorem Equation3698_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3698 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq66 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X3 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2.2 in 14
  have eq93 (X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq9 eq66 -- forward demodulation 66,9
  have eq115 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq93 eq10 -- superposition 10,93, 93 into 10, unify on (0).2 in 93 and (0).2 in 10
  subsumption eq115 rfl


@[equational_result]
theorem Equation3738_implies_Equation4519 (G : Type*) [Magma G] (h : Equation3738 G) : Equation4519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK3) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X4) = ((X0 ◇ X2) ◇ (X4 ◇ X5)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X1)) = ((X4 ◇ X5) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq13 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = (X0 ◇ X4) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq15 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq36 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq15 eq14 -- superposition 14,15, 15 into 14, unify on (0).2 in 15 and (0).1 in 14
  subsumption eq36 rfl


@[equational_result]
theorem Equation3740_implies_Equation3334 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq753 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq193 eq10 -- superposition 10,193, 193 into 10, unify on (0).2 in 193 and (0).2 in 10
  subsumption eq753 rfl


@[equational_result]
theorem Equation3740_implies_Equation4146 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq151 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq47 -- superposition 47,9, 9 into 47, unify on (0).2 in 9 and (0).2.2 in 47
  have eq158 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq193 (X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq9 eq151 -- forward demodulation 151,9
  have eq276 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := superpose eq158 eq10 -- backward demodulation 10,158
  have eq603 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK2 ◇ sK2) ◇ sK1)) := superpose eq158 eq276 -- superposition 276,158, 158 into 276, unify on (0).2 in 158 and (0).2 in 276
  have eq616 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := superpose eq158 eq603 -- forward demodulation 603,158
  subsumption eq616 eq193


@[equational_result]
theorem Equation3740_implies_Equation4512 (G : Type*) [Magma G] (h : Equation3740 G) : Equation4512 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq17 -- superposition 17,12, 12 into 17, unify on (0).2 in 12 and (0).1 in 17
  have eq158 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq47 -- superposition 47,11, 11 into 47, unify on (0).2 in 11 and (0).2 in 47
  have eq638 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose eq158 eq10 -- superposition 10,158, 158 into 10, unify on (0).2 in 158 and (0).2 in 10
  subsumption eq638 rfl


@[equational_result]
theorem Equation3750_implies_Equation3358 (G : Type*) [Magma G] (h : Equation3750 G) : Equation3358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2 in 11
  have eq120 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq11 eq30 -- superposition 30,11, 11 into 30, unify on (0).2 in 11 and (0).2 in 30
  have eq134 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq120 -- forward demodulation 120,9
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq134 eq16 -- backward demodulation 16,134
  have eq167 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq134 -- superposition 134,9, 9 into 134, unify on (0).2 in 9 and (0).2.1 in 134
  have eq172 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq134 eq134 -- superposition 134,134, 134 into 134, unify on (0).2 in 134 and (0).2.1 in 134
  have eq181 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq134 eq15 -- superposition 15,134, 134 into 15, unify on (0).2 in 134 and (0).2.1 in 15
  have eq185 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq167 -- forward demodulation 167,9
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq172 -- forward demodulation 172,9
  have eq215 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq185 eq181 -- forward demodulation 181,185
  have eq216 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq209 eq215 -- forward demodulation 215,209
  have eq217 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq216 eq136 -- backward demodulation 136,216
  have eq218 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq217 eq12 -- backward demodulation 12,217
  have eq231 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK2 ◇ sK0)) := superpose eq217 eq10 -- backward demodulation 10,217
  have eq232 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq218 -- forward demodulation 218,9
  have eq264 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq232 eq217 -- superposition 217,232, 232 into 217, unify on (0).2 in 232 and (0).2 in 217
  have eq271 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq217 eq231 -- superposition 231,217, 217 into 231, unify on (0).2 in 217 and (0).2 in 231
  subsumption eq271 eq264


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
theorem Equation3806_implies_Equation4195 (G : Type*) [Magma G] (h : Equation3806 G) : Equation4195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.2 in 9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2 in 11
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.2 in 11
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.2 in 12
  have eq33 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq51 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq9 eq17 -- superposition 17,9, 9 into 17, unify on (0).2 in 9 and (0).1.2 in 17
  have eq92 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq18 eq51 -- forward demodulation 51,18
  have eq93 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq92 eq30 -- backward demodulation 30,92
  have eq134 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq12 eq33 -- superposition 33,12, 12 into 33, unify on (0).2 in 12 and (0).2 in 33
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq134 -- forward demodulation 134,9
  have eq159 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq152 eq93 -- backward demodulation 93,152
  have eq183 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := superpose eq9 eq152 -- superposition 152,9, 9 into 152, unify on (0).2 in 9 and (0).2.2 in 152
  have eq201 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq183 -- forward demodulation 183,9
  have eq202 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq201 eq12 -- backward demodulation 12,201
  have eq242 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq9 eq202 -- superposition 202,9, 9 into 202, unify on (0).2 in 9 and (0).2.2 in 202
  have eq252 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq201 eq242 -- forward demodulation 242,201
  have eq253 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq252 eq159 -- backward demodulation 159,252
  have eq254 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq253 eq11 -- backward demodulation 11,253
  have eq266 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK0) ◇ sK0) := superpose eq253 eq10 -- backward demodulation 10,253
  have eq267 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ (X1 ◇ X2)) := superpose eq9 eq254 -- forward demodulation 254,9
  have eq300 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ X2) := superpose eq267 eq253 -- superposition 253,267, 267 into 253, unify on (0).2 in 267 and (0).2 in 253
  have eq302 : (sK0 ◇ sK1) ≠ (sK2 ◇ sK0) := superpose eq253 eq266 -- superposition 266,253, 253 into 266, unify on (0).2 in 253 and (0).2 in 266
  subsumption eq302 eq300


@[equational_result]
theorem Equation384_implies_Equation3456 (G : Type*) [Magma G] (h : Equation384 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose eq8 eq9 -- forward demodulation 9,8
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq14 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq11 -- superposition 11,8, 8 into 11, unify on (0).2 in 8 and (0).2 in 11
  have eq17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2 in 10
  subsumption eq17 rfl


@[equational_result]
theorem Equation384_implies_Equation3659 (G : Type*) [Magma G] (h : Equation384 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq13 eq8 -- superposition 8,13, 13 into 8, unify on (0).2 in 13 and (0).2.1 in 8
  have eq19 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq17 -- forward demodulation 17,8
  have eq21 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2 in 9
  subsumption eq21 rfl


@[equational_result]
theorem Equation384_implies_Equation3862 (G : Type*) [Magma G] (h : Equation384 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq8 eq10 -- superposition 10,8, 8 into 10, unify on (0).2 in 8 and (0).2 in 10
  have eq17 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose eq13 eq9 -- backward demodulation 9,13
  subsumption eq17 eq8


@[equational_result]
theorem Equation3869_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3869 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X2 ◇ (X0 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq36 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq36 rfl


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
theorem Equation3875_implies_Equation3872 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3872 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X3 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq31 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq31 rfl


@[equational_result]
theorem Equation3879_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3879 G) : Equation3908 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq12 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq20 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq45 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq20 eq13 -- superposition 13,20, 20 into 13, unify on (0).2 in 20 and (0).2 in 13
  subsumption eq45 eq20


@[equational_result]
theorem Equation3882_implies_Equation3904 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3904 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK3) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).2 in 15
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


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
theorem Equation3885_implies_Equation3912 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK3) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


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
theorem Equation3889_implies_Equation3896 (G : Type*) [Magma G] (h : Equation3889 G) : Equation3896 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK3) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq17 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq18 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq27 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq18 eq18 -- superposition 18,18, 18 into 18, unify on (0).2 in 18 and (0).2 in 18
  have eq54 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq17 -- superposition 17,27, 27 into 17, unify on (0).2 in 27 and (0).2 in 17
  subsumption eq54 eq27


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
theorem Equation3896_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3896 G) : Equation3907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1.2 in 9
  have eq29 (X0 : G) : (sK0 ◇ sK0) ≠ ((sK1 ◇ (X0 ◇ X0)) ◇ sK2) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1.2 in 10
  subsumption eq29 eq27


@[equational_result]
theorem Equation3898_implies_Equation3873 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3894 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3894 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3902 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3902 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3898_implies_Equation3910 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) := mod_symm nh
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq55 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq27 eq16 -- superposition 16,27, 27 into 16, unify on (0).2 in 27 and (0).2 in 16
  subsumption eq55 eq27


@[equational_result]
theorem Equation3899_implies_Equation3911 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3911 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK2) := mod_symm nh
  have eq15 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq23 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq50 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq23 eq16 -- superposition 16,23, 23 into 16, unify on (0).2 in 23 and (0).2 in 16
  subsumption eq50 eq23


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
theorem Equation3910_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3910 G) : Equation3693 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK3)) := mod_symm nh
  have eq16 (X3 X4 : G) : (X4 ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2 in 9
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq16 eq9 -- superposition 9,16, 16 into 9, unify on (0).2 in 16 and (0).2.1 in 9
  have eq26 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK2 ◇ sK3)) := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2.1 in 10
  subsumption eq26 eq25


@[equational_result]
theorem Equation3919_implies_Equation323 (G : Type*) [Magma G] (h : Equation3919 G) : Equation323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3919_implies_Equation3513 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3919_implies_Equation379 (G : Type*) [Magma G] (h : Equation3919 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3919_implies_Equation4400 (G : Type*) [Magma G] (h : Equation3919 G) : Equation4400 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq30 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq30 rfl


@[equational_result]
theorem Equation3926_implies_Equation325 (G : Type*) [Magma G] (h : Equation3926 G) : Equation325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3926_implies_Equation3520 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3520 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3926_implies_Equation379 (G : Type*) [Magma G] (h : Equation3926 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3926_implies_Equation4437 (G : Type*) [Magma G] (h : Equation3926 G) : Equation4437 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3929_implies_Equation326 (G : Type*) [Magma G] (h : Equation3929 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq27 rfl


@[equational_result]
theorem Equation3929_implies_Equation3523 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3523 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).2 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3929_implies_Equation379 (G : Type*) [Magma G] (h : Equation3929 G) : Equation379 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq18 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- superposition 10,13, 13 into 10, unify on (0).2 in 13 and (0).2 in 10
  subsumption eq18 rfl


@[equational_result]
theorem Equation3929_implies_Equation4474 (G : Type*) [Magma G] (h : Equation3929 G) : Equation4474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose eq13 eq10 -- backward demodulation 10,13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq28 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq14 -- superposition 14,18, 18 into 14, unify on (0).2 in 18 and (0).1 in 14
  subsumption eq28 rfl


@[equational_result]
theorem Equation3930_implies_Equation3723 (G : Type*) [Magma G] (h : Equation3930 G) : Equation3723 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ X0) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq17 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq17 eq9 -- backward demodulation 9,17
  have eq35 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq35 eq26


@[equational_result]
theorem Equation3933_implies_Equation4513 (G : Type*) [Magma G] (h : Equation3933 G) : Equation4513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK0 ◇ sK1) ◇ sK3) := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ sK1) := superpose eq14 eq10 -- backward demodulation 10,14
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq14 -- superposition 14,9, 9 into 14, unify on (0).2 in 9 and (0).2 in 14
  have eq29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq18 eq15 -- superposition 15,18, 18 into 15, unify on (0).2 in 18 and (0).1 in 15
  subsumption eq29 rfl


@[equational_result]
theorem Equation3940_implies_Equation3737 (G : Type*) [Magma G] (h : Equation3940 G) : Equation3737 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK2)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq3971 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := superpose eq966 eq10 -- superposition 10,966, 966 into 10, unify on (0).2 in 966 and (0).2 in 10
  have eq4061 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := superpose eq966 eq3971 -- forward demodulation 3971,966
  subsumption eq4061 eq519


@[equational_result]
theorem Equation3940_implies_Equation4143 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).2 in 21
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq58 eq9 -- superposition 9,58, 58 into 9, unify on (0).2 in 58 and (0).2.1 in 9
  have eq251 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := superpose eq164 eq10 -- backward demodulation 10,164
  have eq511 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq59 -- superposition 59,11, 11 into 59, unify on (0).2 in 11 and (0).2 in 59
  have eq734 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2) := superpose eq511 eq251 -- backward demodulation 251,511
  subsumption eq734 eq9


@[equational_result]
theorem Equation3940_implies_Equation4477 (G : Type*) [Magma G] (h : Equation3940 G) : Equation4477 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X1))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq17 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X2))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.2.2 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq9 eq21 -- superposition 21,9, 9 into 21, unify on (0).2 in 9 and (0).2 in 21
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = ((X5 ◇ (X0 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq134 (X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = (X5 ◇ (X1 ◇ (X4 ◇ X2))) := superpose eq17 eq109 -- forward demodulation 109,17
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose eq9 eq58 -- superposition 58,9, 9 into 58, unify on (0).2 in 9 and (0).2.1 in 58
  have eq192 (X1 X2 X3 X4 X5 : G) : (X5 ◇ (X1 ◇ (X4 ◇ X2))) = (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq143 eq134 -- backward demodulation 134,143
  have eq261 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X5) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1.1.2.1 in 16
  have eq269 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).1.1.2 in 16
  have eq279 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq12 eq16 -- superposition 16,12, 12 into 16, unify on (0).2 in 12 and (0).1 in 16
  have eq280 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq16 -- superposition 16,9, 9 into 16, unify on (0).2 in 9 and (0).1 in 16
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X1))) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq143 eq261 -- forward demodulation 261,143
  have eq304 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X5 ◇ X1)))) := superpose eq143 eq303 -- forward demodulation 303,143
  have eq305 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X5)) = ((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X2))) := superpose eq192 eq304 -- forward demodulation 304,192
  have eq332 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq143 eq269 -- forward demodulation 269,143
  have eq333 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = ((X4 ◇ X1) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq305 eq332 -- forward demodulation 332,305
  have eq502 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = ((X4 ◇ (X6 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X3))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2.2.2 in 17
  have eq519 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ (X2 ◇ X2))) := superpose eq11 eq17 -- superposition 17,11, 11 into 17, unify on (0).2 in 11 and (0).2 in 17
  have eq520 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq21 eq17 -- superposition 17,21, 21 into 17, unify on (0).2 in 21 and (0).2 in 17
  have eq572 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ (X3 ◇ X2))))) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq17 eq502 -- forward demodulation 502,17
  have eq573 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X3))) = (X4 ◇ ((X0 ◇ X3) ◇ (X5 ◇ (X1 ◇ X1)))) := superpose eq333 eq572 -- forward demodulation 572,333
  have eq574 (X0 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X5)) = (X4 ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq279 eq573 -- forward demodulation 573,279
  have eq578 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq574 eq280 -- backward demodulation 280,574
  have eq585 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq574 eq12 -- backward demodulation 12,574
  have eq754 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq519 eq578 -- backward demodulation 578,519
  have eq755 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq574 eq520 -- forward demodulation 520,574
  have eq756 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ X2)) := superpose eq519 eq755 -- forward demodulation 755,519
  have eq810 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq17 eq519 -- superposition 519,17, 17 into 519, unify on (0).2 in 17 and (0).2 in 519
  have eq851 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq9 eq810 -- forward demodulation 810,9
  have eq902 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq519 eq585 -- superposition 585,519, 519 into 585, unify on (0).2 in 519 and (0).2.1.2 in 585
  have eq966 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = (X3 ◇ (X0 ◇ X1)) := superpose eq754 eq902 -- forward demodulation 902,754
  have eq967 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq966 eq21 -- backward demodulation 21,966
  have eq999 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X0 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) := superpose eq966 eq585 -- backward demodulation 585,966
  have eq1458 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq9 eq999 -- superposition 999,9, 9 into 999, unify on (0).2 in 9 and (0).2 in 999
  have eq1690 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq17 eq967 -- superposition 967,17, 17 into 967, unify on (0).2 in 17 and (0).1 in 967
  have eq1740 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq1458 eq1690 -- forward demodulation 1690,1458
  have eq1741 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose eq851 eq1740 -- forward demodulation 1740,851
  have eq1836 (X0 : G) : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose eq756 eq10 -- superposition 10,756, 756 into 10, unify on (0).2 in 756 and (0).2 in 10
  subsumption eq1836 eq1741


@[equational_result]
theorem Equation3957_implies_Equation3971 (G : Type*) [Magma G] (h : Equation3957 G) : Equation3971 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X3 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1.2.2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq20 (X0 X1 X2 X4 : G) : (X0 ◇ X4) = ((X4 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.2 in 9
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = ((X4 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq36 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) := superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2 in 12
  have eq41 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1.1.1 in 19
  have eq45 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2.1.1 in 19
  have eq49 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq19 eq19 -- superposition 19,19, 19 into 19, unify on (0).2 in 19 and (0).2.1 in 19
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X0)) := superpose eq11 eq19 -- superposition 19,11, 11 into 19, unify on (0).2 in 11 and (0).2.1 in 19
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq9 eq19 -- superposition 19,9, 9 into 19, unify on (0).2 in 9 and (0).2 in 19
  have eq87 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X0)) := superpose eq19 eq20 -- superposition 20,19, 19 into 20, unify on (0).2 in 19 and (0).2 in 20
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X0)) := superpose eq52 eq87 -- forward demodulation 87,52
  have eq110 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).1 in 45
  have eq113 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq45 eq45 -- superposition 45,45, 45 into 45, unify on (0).2 in 45 and (0).2.1 in 45
  have eq121 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq45 eq19 -- superposition 19,45, 45 into 19, unify on (0).2 in 45 and (0).2.1 in 19
  have eq125 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1.2 in 9
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1.2 in 11
  have eq132 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq45 eq11 -- superposition 11,45, 45 into 11, unify on (0).2 in 45 and (0).2.1 in 11
  have eq133 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq45 eq9 -- superposition 9,45, 45 into 9, unify on (0).2 in 45 and (0).2.1 in 9
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3)) ◇ X0) := superpose eq45 eq12 -- superposition 12,45, 45 into 12, unify on (0).2 in 45 and (0).1.2 in 12
  have eq139 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq121 eq113 -- backward demodulation 113,121
  have eq141 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq121 eq110 -- backward demodulation 110,121
  have eq145 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq121 eq125 -- forward demodulation 125,121
  have eq147 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq121 eq127 -- forward demodulation 127,121
  have eq155 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq121 eq132 -- forward demodulation 132,121
  have eq156 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq121 eq133 -- forward demodulation 133,121
  have eq157 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq156 eq12 -- backward demodulation 12,156
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq156 eq24 -- backward demodulation 24,156
  have eq185 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X0)) := superpose eq156 eq102 -- backward demodulation 102,156
  have eq203 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq15 eq185 -- forward demodulation 185,15
  have eq205 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq121 eq134 -- forward demodulation 134,121
  have eq208 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq9 eq157 -- superposition 157,9, 9 into 157, unify on (0).2 in 9 and (0).1.2.2.1 in 157
  have eq227 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq121 -- superposition 121,9, 9 into 121, unify on (0).2 in 9 and (0).2.1 in 121
  have eq229 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq121 eq121 -- superposition 121,121, 121 into 121, unify on (0).2 in 121 and (0).2.1 in 121
  have eq241 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq227 eq156 -- backward demodulation 156,227
  have eq242 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq227 eq157 -- backward demodulation 157,227
  have eq243 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq227 eq163 -- backward demodulation 163,227
  have eq252 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq227 eq205 -- backward demodulation 205,227
  have eq253 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = ((X0 ◇ X3) ◇ X0) := superpose eq241 eq15 -- backward demodulation 15,241
  have eq255 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq253 eq203 -- backward demodulation 203,253
  have eq258 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = ((((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq253 eq36 -- backward demodulation 36,253
  have eq259 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq9 eq258 -- forward demodulation 258,9
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq252 -- forward demodulation 252,9
  have eq267 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq229 eq49 -- backward demodulation 49,229
  have eq271 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq229 eq141 -- backward demodulation 141,229
  have eq272 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq229 eq227 -- backward demodulation 227,229
  have eq275 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ (X0 ◇ X1)) := superpose eq229 eq242 -- backward demodulation 242,229
  have eq276 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq229 eq243 -- backward demodulation 243,229
  have eq281 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = (X0 ◇ (X3 ◇ X0)) := superpose eq229 eq253 -- backward demodulation 253,229
  have eq282 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq229 eq255 -- backward demodulation 255,229
  have eq304 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) := superpose eq121 eq275 -- superposition 275,121, 121 into 275, unify on (0).2 in 121 and (0).1.2 in 275
  have eq319 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) := superpose eq263 eq304 -- forward demodulation 304,263
  have eq342 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq121 eq281 -- superposition 281,121, 121 into 281, unify on (0).2 in 121 and (0).1.2 in 281
  have eq354 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq281 eq121 -- superposition 121,281, 281 into 121, unify on (0).2 in 281 and (0).2.1 in 121
  have eq366 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq229 -- superposition 229,9, 9 into 229, unify on (0).2 in 9 and (0).1.1 in 229
  have eq369 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq229 eq229 -- superposition 229,229, 229 into 229, unify on (0).2 in 229 and (0).1.1 in 229
  have eq370 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq275 eq229 -- superposition 229,275, 275 into 229, unify on (0).2 in 275 and (0).1.1 in 229
  have eq371 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq281 eq229 -- superposition 229,281, 281 into 229, unify on (0).2 in 281 and (0).1.1 in 229
  have eq372 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq229 -- superposition 229,9, 9 into 229, unify on (0).2 in 9 and (0).1 in 229
  have eq390 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq272 eq366 -- forward demodulation 366,272
  have eq391 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq145 eq369 -- forward demodulation 369,145
  have eq392 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq229 eq391 -- forward demodulation 391,229
  have eq393 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq267 eq370 -- forward demodulation 370,267
  have eq394 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq393 eq319 -- backward demodulation 319,393
  have eq395 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq394 eq259 -- backward demodulation 259,394
  have eq404 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq267 eq371 -- forward demodulation 371,267
  have eq405 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose eq404 eq342 -- backward demodulation 342,404
  have eq407 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq405 eq147 -- backward demodulation 147,405
  have eq409 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq229 eq372 -- forward demodulation 372,229
  have eq410 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq409 eq282 -- backward demodulation 282,409
  have eq417 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq410 eq392 -- backward demodulation 392,410
  have eq420 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X0)) = (X2 ◇ X2) := superpose eq410 eq395 -- backward demodulation 395,410
  have eq432 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq410 eq407 -- backward demodulation 407,410
  have eq436 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq410 eq51 -- backward demodulation 51,410
  have eq469 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq420 -- superposition 420,9, 9 into 420, unify on (0).2 in 9 and (0).1.2 in 420
  have eq494 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq469 eq272 -- backward demodulation 272,469
  have eq497 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq494 eq271 -- backward demodulation 271,494
  have eq500 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ X1) := superpose eq494 eq275 -- backward demodulation 275,494
  have eq501 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq494 eq276 -- backward demodulation 276,494
  have eq513 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq494 eq354 -- backward demodulation 354,494
  have eq519 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) := superpose eq494 eq390 -- backward demodulation 390,494
  have eq524 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq494 eq417 -- backward demodulation 417,494
  have eq534 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X1) ◇ X0) := superpose eq432 eq519 -- forward demodulation 519,432
  have eq536 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq534 eq436 -- backward demodulation 436,534
  have eq546 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq410 -- superposition 410,9, 9 into 410, unify on (0).2 in 9 and (0).1.2 in 410
  have eq564 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq546 eq536 -- backward demodulation 536,546
  have eq571 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq500 -- superposition 500,9, 9 into 500, unify on (0).2 in 9 and (0).1.2.2.1 in 500
  have eq574 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq139 eq500 -- superposition 500,139, 139 into 500, unify on (0).2 in 139 and (0).1.2.2.1 in 500
  have eq589 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq420 eq500 -- superposition 500,420, 420 into 500, unify on (0).2 in 420 and (0).1.2 in 500
  have eq591 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := superpose eq500 eq500 -- superposition 500,500, 500 into 500, unify on (0).2 in 500 and (0).1.2 in 500
  have eq604 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq546 eq571 -- forward demodulation 571,546
  have eq605 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq604 eq208 -- backward demodulation 208,604
  have eq609 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq605 eq155 -- backward demodulation 155,605
  have eq610 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3) := superpose eq609 eq41 -- backward demodulation 41,609
  have eq618 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq524 eq589 -- forward demodulation 589,524
  have eq626 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq618 eq546 -- backward demodulation 546,618
  have eq631 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq626 eq564 -- backward demodulation 564,626
  have eq641 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ X3) := superpose eq626 eq610 -- backward demodulation 610,626
  have eq646 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq497 eq631 -- forward demodulation 631,497
  have eq653 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq646 eq574 -- backward demodulation 574,646
  have eq654 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq653 eq513 -- backward demodulation 513,653
  have eq657 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq654 eq10 -- backward demodulation 10,654
  have eq659 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq646 eq641 -- forward demodulation 641,646
  have eq670 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = ((X4 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq659 eq22 -- backward demodulation 22,659
  have eq679 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = (X1 ◇ X4) := superpose eq9 eq670 -- forward demodulation 670,9
  have eq685 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq11 eq591 -- superposition 591,11, 11 into 591, unify on (0).2 in 11 and (0).1 in 591
  have eq703 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq591 eq11 -- superposition 11,591, 591 into 11, unify on (0).2 in 591 and (0).2 in 11
  have eq724 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq659 eq685 -- forward demodulation 685,659
  have eq725 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq618 eq724 -- forward demodulation 724,618
  have eq726 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq646 eq725 -- forward demodulation 725,646
  have eq731 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq726 eq703 -- forward demodulation 703,726
  have eq732 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq646 eq731 -- forward demodulation 731,646
  have eq733 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq659 eq732 -- forward demodulation 732,659
  have eq737 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4))) := superpose eq733 eq501 -- backward demodulation 501,733
  have eq778 (X0 X1 X3 X4 : G) : (X1 ◇ X4) = ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4) := superpose eq733 eq679 -- backward demodulation 679,733
  have eq797 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq733 eq737 -- forward demodulation 737,733
  have eq798 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq733 eq797 -- forward demodulation 797,733
  have eq799 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X5) := superpose eq733 eq798 -- forward demodulation 798,733
  have eq800 (X0 X1 X2 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X5) := superpose eq733 eq799 -- forward demodulation 799,733
  have eq801 (X0 X1 X5 : G) : ((X5 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X5) := superpose eq733 eq800 -- forward demodulation 800,733
  have eq802 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq121 eq801 -- forward demodulation 801,121
  have eq838 (X0 X1 X4 : G) : (X1 ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ X4) := superpose eq733 eq778 -- forward demodulation 778,733
  have eq839 (X1 X4 : G) : (X1 ◇ X4) = ((X1 ◇ X1) ◇ X4) := superpose eq494 eq838 -- forward demodulation 838,494
  have eq853 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq591 eq839 -- superposition 839,591, 591 into 839, unify on (0).2 in 591 and (0).2.1 in 839
  have eq866 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose eq733 eq853 -- forward demodulation 853,733
  have eq874 (X0 X1 X5 : G) : (X0 ◇ X5) = ((X5 ◇ X0) ◇ X1) := superpose eq866 eq802 -- backward demodulation 802,866
  have eq901 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq839 eq874 -- superposition 874,839, 839 into 874, unify on (0).2 in 839 and (0).2 in 874
  have eq932 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq901 eq657 -- superposition 657,901, 901 into 657, unify on (0).2 in 901 and (0).1 in 657
  subsumption eq932 rfl


@[equational_result]
theorem Equation3967_implies_Equation3561 (G : Type*) [Magma G] (h : Equation3967 G) : Equation3561 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X2)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq11 -- forward demodulation 11,9
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) = (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).1.2.2 in 13
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).1.2 in 13
  have eq24 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X4))) = (((X2 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1.1 in 13
  have eq27 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2.1 in 13
  have eq28 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X1 ◇ X4))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq13 eq13 -- superposition 13,13, 13 into 13, unify on (0).2 in 13 and (0).2.1 in 13
  have eq34 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ (((X3 ◇ X1) ◇ X1) ◇ X0)) ◇ X4) := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2.1.2 in 9
  have eq37 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq9 eq15 -- forward demodulation 15,9
  have eq42 (X1 X3 X4 : G) : (X3 ◇ X1) = (X3 ◇ (X1 ◇ (X1 ◇ X4))) := superpose eq9 eq28 -- forward demodulation 28,9
  have eq43 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = (X3 ◇ X2) := superpose eq42 eq24 -- backward demodulation 24,42
  have eq45 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = (((X4 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) := superpose eq42 eq37 -- backward demodulation 37,42
  have eq46 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq13 -- backward demodulation 13,42
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq42 eq27 -- backward demodulation 27,42
  have eq49 (X0 X1 X2 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq50 (X0 X2 X3 X4 : G) : (((X4 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq42 eq45 -- forward demodulation 45,42
  have eq54 (X0 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq46 eq50 -- backward demodulation 50,46
  have eq60 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq43 eq47 -- forward demodulation 47,43
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq60 eq9 -- backward demodulation 9,60
  have eq69 (X0 X1 X2 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq46 eq49 -- forward demodulation 49,46
  have eq70 (X0 X1 X4 X5 : G) : (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) = (X4 ◇ X1) := superpose eq54 eq69 -- forward demodulation 69,54
  have eq71 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X4) := superpose eq60 eq70 -- forward demodulation 70,60
  have eq72 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X4) := superpose eq60 eq71 -- forward demodulation 71,60
  have eq73 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = (((X5 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) := superpose eq60 eq72 -- forward demodulation 72,60
  have eq74 (X0 X1 X4 X5 : G) : (((X5 ◇ X0) ◇ X0) ◇ X4) = (X4 ◇ X1) := superpose eq60 eq73 -- forward demodulation 73,60
  have eq85 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X4) := superpose eq60 eq34 -- forward demodulation 34,60
  have eq86 (X0 X1 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ (X3 ◇ X1)) ◇ X4) := superpose eq60 eq85 -- forward demodulation 85,60
  have eq87 (X0 X3 X4 : G) : (X4 ◇ X0) = ((X0 ◇ X3) ◇ X4) := superpose eq60 eq86 -- forward demodulation 86,60
  have eq93 (X0 X1 X4 X5 : G) : (X4 ◇ X1) = ((X0 ◇ X5) ◇ X4) := superpose eq87 eq74 -- backward demodulation 74,87
  have eq95 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq87 eq10 -- backward demodulation 10,87
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq61 eq93 -- superposition 93,61, 61 into 93, unify on (0).2 in 61 and (0).2 in 93
  have eq168 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ X4) := superpose eq93 eq145 -- superposition 145,93, 93 into 145, unify on (0).2 in 93 and (0).1 in 145
  have eq195 (X0 : G) : (sK0 ◇ sK1) ≠ (sK1 ◇ X0) := superpose eq145 eq95 -- superposition 95,145, 145 into 95, unify on (0).2 in 145 and (0).2 in 95
  have eq253 (X1 X2 : G) : (sK0 ◇ sK1) ≠ ((X1 ◇ X2) ◇ sK1) := superpose eq93 eq195 -- superposition 195,93, 93 into 195, unify on (0).2 in 93 and (0).2 in 195
  subsumption eq253 eq168


@[equational_result]
theorem Equation3971_implies_Equation3347 (G : Type*) [Magma G] (h : Equation3971 G) : Equation3347 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (((X2 ◇ X3) ◇ X0) ◇ X2) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((X3 ◇ X0) ◇ X1) ◇ X0) ◇ X1) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1 in 11
  have eq44 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X1) := superpose eq28 eq28 -- superposition 28,28, 28 into 28, unify on (0).2 in 28 and (0).2.1 in 28
  have eq52 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq28 eq11 -- superposition 11,28, 28 into 11, unify on (0).2 in 28 and (0).2.1.2 in 11
  have eq56 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq28 eq9 -- superposition 9,28, 28 into 9, unify on (0).2 in 28 and (0).2.1 in 9
  have eq77 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) = (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq12 eq15 -- superposition 15,12, 12 into 15, unify on (0).2 in 12 and (0).1.2 in 15
  have eq93 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ X2) := superpose eq9 eq77 -- forward demodulation 77,9
  have eq94 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) := superpose eq44 eq93 -- forward demodulation 93,44
  have eq99 (X1 X2 X3 : G) : (X3 ◇ X1) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq94 eq56 -- backward demodulation 56,94
  have eq100 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) = ((X3 ◇ (X2 ◇ X1)) ◇ X1) := superpose eq94 eq52 -- backward demodulation 52,94
  have eq112 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq99 eq94 -- backward demodulation 94,99
  have eq115 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ X0) := superpose eq112 eq9 -- backward demodulation 9,112
  have eq132 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK1)) := superpose eq112 eq10 -- backward demodulation 10,112
  have eq147 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) := superpose eq115 eq100 -- forward demodulation 100,115
  have eq148 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq115 eq147 -- forward demodulation 147,115
  have eq149 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ X3) := superpose eq112 eq148 -- forward demodulation 148,112
  have eq175 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq115 eq115 -- superposition 115,115, 115 into 115, unify on (0).2 in 115 and (0).2.1 in 115
  have eq176 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq112 eq175 -- forward demodulation 175,112
  have eq179 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ X1) := superpose eq115 eq176 -- superposition 176,115, 115 into 176, unify on (0).2 in 115 and (0).2 in 176
  have eq183 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq176 eq179 -- superposition 179,176, 176 into 179, unify on (0).2 in 176 and (0).1 in 179
  have eq195 (X0 : G) : (sK0 ◇ X0) ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose eq179 eq132 -- superposition 132,179, 179 into 132, unify on (0).2 in 179 and (0).1 in 132
  have eq230 (X0 X1 : G) : (sK0 ◇ X0) ≠ (sK1 ◇ X1) := superpose eq179 eq195 -- superposition 195,179, 179 into 195, unify on (0).2 in 179 and (0).2 in 195
  have eq352 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq44 eq149 -- superposition 149,44, 44 into 149, unify on (0).2 in 44 and (0).2 in 149
  have eq410 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X1) := superpose eq149 eq183 -- superposition 183,149, 149 into 183, unify on (0).2 in 149 and (0).2 in 183
  have eq500 (X0 X1 : G) : (sK1 ◇ X1) ≠ (X0 ◇ sK0) := superpose eq352 eq230 -- superposition 230,352, 352 into 230, unify on (0).2 in 352 and (0).1 in 230
  subsumption eq500 eq410


@[equational_result]
theorem Equation3973_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3973 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X3 ◇ X0) ◇ X2) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).1 in 21
  have eq60 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2))) := superpose eq21 eq11 -- superposition 11,21, 21 into 11, unify on (0).2 in 21 and (0).2.1 in 11
  have eq192 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ X0) ◇ X3) := superpose eq56 eq56 -- superposition 56,56, 56 into 56, unify on (0).2 in 56 and (0).1.1 in 56
  have eq309 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X3))) := superpose eq9 eq15 -- superposition 15,9, 9 into 15, unify on (0).2 in 9 and (0).2 in 15
  have eq357 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (X2 ◇ (((X4 ◇ X3) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq192 eq309 -- forward demodulation 309,192
  have eq358 (X0 X2 X4 : G) : (X4 ◇ X0) = (X2 ◇ (X2 ◇ (X4 ◇ X0))) := superpose eq60 eq357 -- forward demodulation 357,60
  have eq422 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq358 eq10 -- superposition 10,358, 358 into 10, unify on (0).2 in 358 and (0).2 in 10
  subsumption eq422 rfl


@[equational_result]
theorem Equation3975_implies_Equation3971 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3971 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.2 in 9
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.2 in 11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2.1.2 in 11
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq32 -- forward demodulation 32,9
  have eq45 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = (X3 ◇ X0) := superpose eq42 eq19 -- backward demodulation 19,42
  have eq58 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq35 -- forward demodulation 35,42
  have eq59 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) := superpose eq42 eq58 -- forward demodulation 58,42
  have eq60 (X0 X1 X3 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X1) ◇ X1) ◇ X4) := superpose eq45 eq59 -- forward demodulation 59,45
  have eq61 (X0 X1 X4 : G) : (X4 ◇ X1) = (X4 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq45 eq60 -- forward demodulation 60,45
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq42 eq42 -- superposition 42,42, 42 into 42, unify on (0).2 in 42 and (0).2.2 in 42
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq61 eq101 -- forward demodulation 101,61
  have eq125 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X2 ◇ X0) ◇ X3) := superpose eq121 eq11 -- backward demodulation 11,121
  have eq126 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose eq121 eq10 -- backward demodulation 10,121
  subsumption eq126 eq125


@[equational_result]
theorem Equation4072_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4072 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq15 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1.1 in 12
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).1 in 12
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).1 in 12
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq17 eq22 -- forward demodulation 22,17
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq32 eq15 -- backward demodulation 15,32
  have eq78 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq18 eq10 -- superposition 10,18, 18 into 10, unify on (0).2 in 18 and (0).2.1 in 10
  subsumption eq78 eq33


@[equational_result]
theorem Equation4075_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4075 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq9 eq14 -- forward demodulation 14,9
  have eq25 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq17 eq10 -- superposition 10,17, 17 into 10, unify on (0).2 in 17 and (0).2 in 10
  subsumption eq25 rfl


@[equational_result]
theorem Equation4078_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4078 G) : Equation4069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq13 -- forward demodulation 13,9
  have eq19 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1.1 in 14
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).1 in 14
  have eq39 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X3) := superpose eq16 eq19 -- forward demodulation 19,16
  have eq122 (X0 : G) : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ X0) ◇ sK2) := superpose eq21 eq10 -- superposition 10,21, 21 into 10, unify on (0).2 in 21 and (0).2.1 in 10
  subsumption eq122 eq39


@[equational_result]
theorem Equation4080_implies_Equation359 (G : Type*) [Magma G] (h : Equation4080 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have eq11 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq11 eq9 -- superposition 9,11, 11 into 9, unify on (0).2 in 11 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation4082_implies_Equation4075 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4108 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4108 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4109 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4082_implies_Equation4111 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4111 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq14 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X3) := superpose eq12 eq11 -- backward demodulation 11,12
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq63 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq28 eq13 -- superposition 13,28, 28 into 13, unify on (0).2 in 28 and (0).2 in 13
  subsumption eq63 eq28


@[equational_result]
theorem Equation4086_implies_Equation4096 (G : Type*) [Magma G] (h : Equation4086 G) : Equation4096 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK0) := mod_symm nh
  have eq12 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X2 ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 : (sK0 ◇ sK0) ≠ ((sK2 ◇ sK2) ◇ sK0) := superpose eq12 eq10 -- backward demodulation 10,12
  subsumption eq13 eq12


@[equational_result]
theorem Equation4088_implies_Equation4078 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4110 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK2) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq28 -- superposition 28,9, 9 into 28, unify on (0).2 in 9 and (0).2 in 28
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4088_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq14 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK2 ◇ sK2) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq14 eq9 -- superposition 9,14, 14 into 9, unify on (0).2 in 14 and (0).2.1 in 9
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X2) := superpose eq9 eq27 -- superposition 27,9, 9 into 27, unify on (0).2 in 9 and (0).2 in 27
  have eq115 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq37 eq16 -- superposition 16,37, 37 into 16, unify on (0).2 in 37 and (0).2 in 16
  subsumption eq115 eq37


@[equational_result]
theorem Equation4102_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq21 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X1) := superpose eq14 eq14 -- superposition 14,14, 14 into 14, unify on (0).2 in 14 and (0).2 in 14
  have eq42 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq21 eq16 -- superposition 16,21, 21 into 16, unify on (0).2 in 21 and (0).2 in 16
  subsumption eq42 eq21


@[equational_result]
theorem Equation4103_implies_Equation4112 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK0) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4114 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK2) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK3) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4103_implies_Equation4116 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4116 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X3) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq15 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X4) = (X3 ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq18 : (sK0 ◇ sK0) ≠ (sK3 ◇ sK3) := superpose eq9 eq10 -- superposition 10,9, 9 into 10, unify on (0).2 in 9 and (0).2 in 10
  have eq24 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X3) := superpose eq15 eq15 -- superposition 15,15, 15 into 15, unify on (0).2 in 15 and (0).1 in 15
  have eq58 (X0 : G) : (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose eq24 eq18 -- superposition 18,24, 24 into 18, unify on (0).2 in 24 and (0).2 in 18
  subsumption eq58 eq24


@[equational_result]
theorem Equation4110_implies_Equation4099 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4099 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ X2) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK2) ◇ sK3) := mod_symm nh
  have eq14 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq47 (X0 : G) : (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK3) := superpose eq14 eq10 -- superposition 10,14, 14 into 10, unify on (0).2 in 14 and (0).2.1 in 10
  subsumption eq47 eq14


@[equational_result]
theorem Equation412_implies_Equation3 (G : Type*) [Magma G] (h : Equation412 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2.2 in 8
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2.2 in 8
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10 -- backward demodulation 10,11
  have eq15 : sK0 ≠ sK0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).2 in 9
  subsumption eq15 rfl


@[equational_result]
theorem Equation4141_implies_Equation4153 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4153 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, sK3, sK4, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK3) ◇ sK4) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1 in 9
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq12 eq9 -- superposition 9,12, 12 into 9, unify on (0).2 in 12 and (0).2.1.1 in 9
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq9 eq17 -- forward demodulation 17,9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1.1 in 11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq12 eq11 -- superposition 11,12, 12 into 11, unify on (0).2 in 12 and (0).2 in 11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9 -- superposition 9,19, 19 into 9, unify on (0).2 in 19 and (0).2.1 in 9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq46 -- forward demodulation 46,9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq19 eq56 -- forward demodulation 56,19
  have eq63 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq12 eq18 -- superposition 18,12, 12 into 18, unify on (0).2 in 12 and (0).2.1.1.1 in 18
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq18 eq12 -- superposition 12,18, 18 into 12, unify on (0).2 in 18 and (0).1.1 in 12
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq57 -- superposition 57,9, 9 into 57, unify on (0).2 in 9 and (0).2.2 in 57
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq12 eq101 -- forward demodulation 101,12
  have eq147 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) := superpose eq18 eq32 -- superposition 32,18, 18 into 32, unify on (0).2 in 18 and (0).1.1 in 32
  have eq154 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq32 eq18 -- superposition 18,32, 32 into 18, unify on (0).2 in 32 and (0).2.1.1 in 18
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq12 eq147 -- forward demodulation 147,12
  have eq228 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq122 eq11 -- superposition 11,122, 122 into 11, unify on (0).2 in 122 and (0).2.1 in 11
  have eq262 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X1) ◇ X0) := superpose eq11 eq228 -- forward demodulation 228,11
  have eq263 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq262 -- forward demodulation 262,9
  have eq265 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq263 eq193 -- backward demodulation 193,263
  have eq266 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq63 -- backward demodulation 63,263
  have eq275 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq263 eq14 -- backward demodulation 14,263
  have eq286 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ X0) := superpose eq263 eq265 -- forward demodulation 265,263
  have eq293 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq286 eq81 -- backward demodulation 81,286
  have eq308 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X2)) := superpose eq263 eq293 -- forward demodulation 293,263
  have eq314 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq308 eq266 -- forward demodulation 266,308
  have eq315 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0)) := superpose eq314 eq20 -- backward demodulation 20,314
  have eq317 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq154 -- backward demodulation 154,314
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq314 eq315 -- forward demodulation 315,314
  have eq345 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq344 -- forward demodulation 344,9
  have eq346 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X3) ◇ X4) := superpose eq345 eq317 -- forward demodulation 317,345
  have eq505 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq286 eq275 -- superposition 275,286, 286 into 275, unify on (0).2 in 286 and (0).2 in 275
  have eq560 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK3) ◇ sK4) := superpose eq505 eq10 -- backward demodulation 10,505
  have eq561 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK0) := superpose eq346 eq560 -- forward demodulation 560,346
  subsumption eq561 eq505


@[equational_result]
theorem Equation414_implies_Equation3659 (G : Type*) [Magma G] (h : Equation414 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).1.2 in 8
  have eq12 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq10 eq9 -- superposition 9,10, 10 into 9, unify on (0).2 in 10 and (0).2 in 9
  subsumption eq12 rfl


@[equational_result]
theorem Equation4154_implies_Equation3253 (G : Type*) [Magma G] (h : Equation4154 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have eq8 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have eq9 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq8 eq8 -- superposition 8,8, 8 into 8, unify on (0).2 in 8 and (0).2.1 in 8
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq8 -- superposition 8,11, 11 into 8, unify on (0).2 in 11 and (0).2.1 in 8
  have eq18 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq15 -- superposition 15,11, 11 into 15, unify on (0).2 in 11 and (0).2 in 15
  have eq22 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq18 -- forward demodulation 18,11
  have eq26 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose eq22 eq9 -- superposition 9,22, 22 into 9, unify on (0).2 in 22 and (0).2 in 9
  subsumption eq26 rfl


@[equational_result]
theorem Equation415_implies_Equation48 (G : Type*) [Magma G] (h : Equation415 G) : Equation48 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation4178_implies_Equation4195 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4195 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (((sK2 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq12 -- forward demodulation 12,9
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ (X0 ◇ X1)) := superpose eq13 eq11 -- backward demodulation 11,13
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (X3 ◇ X0) := superpose eq13 eq14 -- forward demodulation 14,13
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq13 eq15 -- forward demodulation 15,13
  have eq17 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X3) := superpose eq13 eq16 -- forward demodulation 16,13
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq13 -- superposition 13,9, 9 into 13, unify on (0).2 in 9 and (0).2 in 13
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ X0) := superpose eq9 eq20 -- forward demodulation 20,9
  have eq27 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq24 eq17 -- backward demodulation 17,24
  have eq28 : (sK0 ◇ sK1) ≠ ((sK2 ◇ sK1) ◇ sK0) := superpose eq24 eq10 -- backward demodulation 10,24
  subsumption eq28 eq27


@[equational_result]
theorem Equation418_implies_Equation1428 (G : Type*) [Magma G] (h : Equation418 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation418_implies_Equation2243 (G : Type*) [Magma G] (h : Equation418 G) : Equation2243 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation418_implies_Equation3255 (G : Type*) [Magma G] (h : Equation418 G) : Equation3255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq14 : sK0 ≠ (sK0 ◇ sK0) := superpose eq11 eq10 -- backward demodulation 10,11
  have eq18 : sK0 ≠ sK0 := superpose eq13 eq14 -- superposition 14,13, 13 into 14, unify on (0).2 in 13 and (0).2 in 14
  subsumption eq18 rfl


@[equational_result]
theorem Equation418_implies_Equation415 (G : Type*) [Magma G] (h : Equation418 G) : Equation415 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := mod_symm nh
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq9 -- superposition 9,13, 13 into 9, unify on (0).2 in 13 and (0).1.2.2 in 9
  have eq32 : sK0 ≠ sK0 := superpose eq16 eq10 -- superposition 10,16, 16 into 10, unify on (0).2 in 16 and (0).2 in 10
  subsumption eq32 rfl


@[equational_result]
theorem Equation418_implies_Equation625 (G : Type*) [Magma G] (h : Equation418 G) : Equation625 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq23 : sK0 ≠ sK0 := superpose eq11 eq10 -- superposition 10,11, 11 into 10, unify on (0).2 in 11 and (0).2 in 10
  subsumption eq23 rfl


@[equational_result]
theorem Equation418_implies_Equation819 (G : Type*) [Magma G] (h : Equation418 G) : Equation819 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2.2.2 in 9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).1.2 in 9
  have eq15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose eq13 eq10 -- backward demodulation 10,13
  subsumption eq15 eq11


@[equational_result]
theorem Equation4195_implies_Equation3348 (G : Type*) [Magma G] (h : Equation4195 G) : Equation3348 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X3) ◇ X1) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq12 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X2) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X2) ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2.1 in 12
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq12 -- superposition 12,12, 12 into 12, unify on (0).2 in 12 and (0).2.1 in 12
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq9 eq12 -- superposition 12,9, 9 into 12, unify on (0).2 in 9 and (0).2 in 12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X2 ◇ X1)) := superpose eq14 eq13 -- backward demodulation 13,14
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ X1) := superpose eq15 eq19 -- backward demodulation 19,15
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14 -- backward demodulation 14,15
  have eq22 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq15 eq10 -- backward demodulation 10,15
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq15 eq9 -- superposition 9,15, 15 into 9, unify on (0).2 in 15 and (0).2.1.1 in 9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq12 eq36 -- forward demodulation 36,12
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq21 -- superposition 21,12, 12 into 21, unify on (0).2 in 12 and (0).1.1 in 21
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq21 eq9 -- superposition 9,21, 21 into 9, unify on (0).2 in 21 and (0).2.1 in 9
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq52 -- forward demodulation 52,46
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq57 eq27 -- backward demodulation 27,57
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq15 eq20 -- superposition 20,15, 15 into 20, unify on (0).2 in 15 and (0).1.2.1 in 20
  have eq89 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq57 eq74 -- forward demodulation 74,57
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq62 eq89 -- forward demodulation 89,62
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq90 eq67 -- backward demodulation 67,90
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq91 eq9 -- backward demodulation 9,91
  have eq97 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ X3) ◇ X1) := superpose eq91 eq11 -- backward demodulation 11,91
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq96 eq96 -- superposition 96,96, 96 into 96, unify on (0).2 in 96 and (0).1 in 96
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq21 eq96 -- superposition 96,21, 21 into 96, unify on (0).2 in 21 and (0).2 in 96
  have eq121 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose eq117 eq22 -- backward demodulation 22,117
  have eq123 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq117 eq117 -- superposition 117,117, 117 into 117, unify on (0).2 in 117 and (0).2 in 117
  have eq128 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := superpose eq117 eq121 -- superposition 121,117, 117 into 121, unify on (0).2 in 117 and (0).2 in 121
  have eq159 (X0 : G) : (sK0 ◇ sK0) ≠ (sK1 ◇ X0) := superpose eq117 eq128 -- superposition 128,117, 117 into 128, unify on (0).2 in 117 and (0).2 in 128
  have eq168 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq97 eq114 -- superposition 114,97, 97 into 114, unify on (0).2 in 97 and (0).2 in 114
  have eq336 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq97 eq168 -- superposition 168,97, 97 into 168, unify on (0).2 in 97 and (0).2 in 168
  have eq594 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X1) := superpose eq123 eq336 -- superposition 336,123, 123 into 336, unify on (0).2 in 123 and (0).1 in 336
  have eq633 (X0 : G) : (sK0 ◇ sK0) ≠ (X0 ◇ X0) := superpose eq336 eq159 -- superposition 159,336, 336 into 159, unify on (0).2 in 336 and (0).2 in 159
  subsumption eq633 eq594


@[equational_result]
theorem Equation4209_implies_Equation385 (G : Type*) [Magma G] (h : Equation4209 G) : Equation385 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have eq12 (X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ X2) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1 in 9
  have eq16 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose eq12 eq10 -- superposition 10,12, 12 into 10, unify on (0).2 in 12 and (0).2 in 10
  subsumption eq16 rfl


@[equational_result]
theorem Equation4212_implies_Equation3750 (G : Type*) [Magma G] (h : Equation4212 G) : Equation3750 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have eq10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK2)) := mod_symm nh
  have eq11 (X1 X2 X3 : G) : (X3 ◇ X2) = (((X2 ◇ X1) ◇ X2) ◇ X3) := superpose eq9 eq9 -- superposition 9,9, 9 into 9, unify on (0).2 in 9 and (0).2.1.1 in 9
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq11 -- superposition 11,9, 9 into 11, unify on (0).2 in 9 and (0).2.1 in 11
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq11 eq11 -- superposition 11,11, 11 into 11, unify on (0).2 in 11 and (0).2.1 in 11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq22 -- forward demodulation 22,9
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq32 eq23 -- forward demodulation 23,32
  have eq74 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X3) := superpose eq9 eq32 -- superposition 32,9, 9 into 32, unify on (0).2 in 9 and (0).2 in 32
  have eq89 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ X3) ◇ X1) := superpose eq9 eq74 -- forward demodulation 74,9
  have eq94 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq89 eq35 -- backward demodulation 35,89
  have eq95 (X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq89 eq11 -- backward demodulation 11,89
  have eq127 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ X0) := superpose eq95 eq94 -- superposition 94,95, 95 into 94, unify on (0).2 in 95 and (0).2 in 94
  have eq146 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X3) := superpose eq94 eq127 -- superposition 127,94, 94 into 127, unify on (0).2 in 94 and (0).1 in 127
  have eq169 (X0 : G) : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ X0) := superpose eq127 eq10 -- superposition 10,127, 127 into 10, unify on (0).2 in 127 and (0).2 in 10
  subsumption eq169 eq146


