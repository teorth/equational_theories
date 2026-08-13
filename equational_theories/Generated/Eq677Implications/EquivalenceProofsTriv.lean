import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import equational_theories.Finite677.Eq19855
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation677_and_Equation1021_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step20 step17
  have step24 (X0 X1 : G) :  X0 = X1 := superpose step20 step21
  have step38 (X0 : G) :  sK0 ≠ X0 := superpose step24 step10
  subsumption step38 step24


@[equational_result]
theorem Finite.Equation677_and_Equation1022_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step9 step9
  have step20 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step11 step9
  have step28 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step37 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose step13 step28
  have step52 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X1 := superpose step11 step20
  have step75 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step52 step12
  have step79 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step52 step75
  have step97 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step37 step12
  have step108 (X0 X1 : G) :  X0 = X1 := superpose step79 step97
  have step136 (X0 : G) :  sK0 ≠ X0 := superpose step108 step10
  subsumption step136 step108


@[equational_result]
theorem Finite.Equation677_and_Equation1025_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step9
  have step21 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step14 step12
  have step28 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose step22 step21
  have step36 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose step28 step11
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step24 step11
  have step47 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step24 step14
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step45
  have step50 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step47 step48
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step50
  have step85 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step28 step23
  have step102 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step36 step85
  have step107 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step51 step102
  have step111 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step28 step107
  have step114 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step51 step111
  have step133 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step114 step23
  have step142 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step133
  have step153 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step51 step142
  have step158 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step51 step153
  have step248 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step158 step12
  have step257 (X0 X1 : G) :  X0 = X1 := superpose step158 step248
  have step371 (X0 : G) :  sK0 ≠ X0 := superpose step257 step10
  subsumption step371 step257


@[equational_result]
theorem Finite.Equation677_and_Equation1028_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step11
  have step16 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step32 (X0 X1 X2 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((X0 ◇ (X2 ◇ X2)) ◇ X0) := superpose step16 step16
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step16 step12
  have step39 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step16 step9
  have step41 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step16 step12
  have step43 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step41
  have step87 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step34 step17
  have step97 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step99 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step87
  have step119 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step16 step32
  have step166 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step9 step119
  have step227 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step39 step11
  have step237 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step39 step17
  have step241 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step166 step237
  have step252 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step227 step241
  have step257 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step15 step252
  have step346 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step99 step32
  have step386 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := superpose step16 step19
  have step426 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := superpose step9 step386
  have step538 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step257 step17
  have step540 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step257 step11
  have step541 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step15 step540
  have step543 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step12 step538
  have step556 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step541
  have step558 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step39 step543
  have step608 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step43 step17
  have step611 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step346 step608
  have step630 (X0 X1 : G) :  (X0 ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step556 step611
  have step723 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step558 step12
  have step724 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step558 step11
  have step1190 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0)) := superpose step724 step17
  have step1195 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose step12 step1190
  have step1364 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step1195 step1195
  have step2852 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step16 step97
  have step2964 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step2852
  have step2991 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step723 step2964
  have step3011 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step630 step2991
  have step3032 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step558 step3011
  have step3088 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step3011 step12
  have step3101 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step227 step3088
  have step3125 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step556 step3101
  have step3181 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ (X2 ◇ X2)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) := superpose step1364 step426
  have step3182 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))))) := superpose step1195 step426
  have step3233 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose step3032 step3182
  have step3234 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ (X2 ◇ X2)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose step3032 step3181
  have step3283 (X0 X1 : G) :  (X1 ◇ X1) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step15 step3233
  have step3284 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) := superpose step15 step3234
  have step3326 (X0 X1 : G) :  (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose step3125 step3283
  have step3327 (X0 X1 X2 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) = X2 := superpose step3125 step3284
  have step3350 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose step556 step3326
  have step3351 (X0 X2 : G) :  (((X0 ◇ X0) ◇ X2) ◇ X2) = X2 := superpose step556 step3327
  have step3367 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose step3032 step3350
  have step3368 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X2) = X2 := superpose step3032 step3351
  have step3377 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose step3032 step3367
  have step3378 (X0 X2 : G) :  (X0 ◇ X2) = X2 := superpose step3125 step3368
  have step3387 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step556 step3377
  have step3391 (X0 X1 : G) :  X0 = X1 := superpose step3378 step3387
  have step3576 (X0 : G) :  sK0 ≠ X0 := superpose step3391 step10
  subsumption step3576 step3391


@[equational_result]
theorem Finite.Equation677_and_Equation1036_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step15 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step15 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step15 step12
  have step31 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step29
  have step56 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) := superpose step15 step16
  have step66 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step23 step56
  have step80 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step66 step9
  have step82 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose step66 step12
  have step112 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step80 step9
  have step118 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step80 step13
  have step120 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step80 step15
  have step127 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step80 step120
  have step128 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step82 step118
  have step133 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step127 step128
  have step134 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step112 step133
  have step147 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step80 step14
  have step158 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)))) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step13 step14
  have step164 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step15 step14
  have step175 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step80 step164
  have step178 (X0 X1 : G) :  (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step31 step158
  have step183 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step134 step147
  have step190 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ X0)) := superpose step134 step175
  have step193 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step16 step178
  have step195 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step183
  have step201 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step190
  have step204 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step80 step193
  have step206 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step112 step195
  have step210 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step80 step201
  have step211 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step15 step204
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step206 step210
  have step215 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step206 step211
  have step218 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step214 step215
  have step221 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step214 step218
  have step223 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step134 step221
  have step225 (X0 X1 : G) :  X0 = X1 := superpose step214 step223
  have step276 (X0 : G) :  sK0 ≠ X0 := superpose step225 step10
  subsumption step276 step225


@[equational_result]
theorem Finite.Equation677_and_Equation1038_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step9 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step22 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step9
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step12
  have step79 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step9
  have step86 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose step18 step56
  have step127 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step79 step12
  have step147 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step79 step19
  have step177 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step12 step147
  have step296 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step177 step79
  have step308 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step177 step86
  have step309 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose step127 step308
  have step577 (X0 : G) :  (X0 ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step177 step22
  have step606 (X0 : G) :  (X0 ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step296 step577
  have step619 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step296 step606
  have step623 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step309 step619
  have step637 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step623 step19
  have step638 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step623 step22
  have step641 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose step623 step86
  have step642 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step296 step641
  have step645 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step127 step638
  have step646 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step623 step637
  have step656 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step296 step642
  have step659 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step177 step646
  have step667 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step645 step656
  have step684 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step18 step21
  have step744 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step659 step684
  have step758 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step9 step744
  have step768 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := superpose step659 step758
  have step774 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose step667 step768
  have step799 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step667 step18
  have step811 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose step645 step799
  have step871 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step774 step19
  have step901 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step811 step871
  have step940 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X0)) := superpose step811 step901
  have step962 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step645 step940
  have step1411 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step962 step14
  have step1454 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step811 step1411
  have step1743 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step1454 step12
  have step1760 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step1454 step962
  have step1777 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step1760 step1743
  have step2003 (X0 X1 : G) :  X0 = X1 := superpose step1777 step11
  have step2303 (X0 : G) :  sK0 ≠ X0 := superpose step2003 step10
  subsumption step2303 step2003


@[equational_result]
theorem Finite.Equation677_and_Equation1046_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step32 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step18 step11
  have step51 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step20 step11
  have step54 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step32 step51
  have step57 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step17 step54
  have step59 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step57 step11
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step57 step12
  have step67 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step63
  have step72 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step57 step19
  have step106 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step72
  have step115 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step18 step106
  have step120 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step67 step115
  have step130 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step120 step18
  have step133 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step59 step130
  have step404 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step18 step15
  have step419 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step57 step404
  have step451 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X0)) := superpose step120 step419
  have step475 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step12 step451
  have step595 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step17 step12
  have step608 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step475 step595
  have step639 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step120 step608
  have step684 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step133 step133
  have step694 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step133 step12
  have step711 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step133 step19
  have step712 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step639 step711
  have step741 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step684 step712
  have step761 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose step18 step21
  have step823 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step741 step761
  have step854 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step694 step823
  have step878 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose step741 step854
  have step887 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step741 step878
  have step892 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step694 step887
  have step964 (X0 X1 : G) :  X0 = X1 := superpose step892 step133
  have step1134 (X0 : G) :  sK0 ≠ X0 := superpose step964 step10
  subsumption step1134 step964


@[equational_result]
theorem Finite.Equation677_and_Equation1049_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step11
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step31 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step9
  have step36 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step31 step25
  have step40 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose step31 step36
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step22 step40
  have step46 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step31 step44
  have step47 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose step31 step9
  have step52 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step31 step47
  have step55 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step31 step52
  have step69 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step46 step31
  have step76 (X0 X1 : G) :  X0 = X1 := superpose step55 step69
  have step102 (X0 : G) :  sK0 ≠ X0 := superpose step76 step10
  subsumption step102 step76


@[equational_result]
theorem Finite.Equation677_and_Equation105_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step9 step11
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step9 step26
  have step36 (X0 X1 : G) :  X0 = X1 := superpose step16 step34
  have step50 (X0 : G) :  sK0 ≠ X0 := superpose step36 step10
  subsumption step50 step36


@[equational_result]
theorem Finite.Equation677_and_Equation107_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step9 step20
  have step32 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step16 step29
  have step55 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step32 step12
  have step56 (X0 X1 : G) :  X0 = X1 := superpose step32 step55
  have step81 (X0 : G) :  sK0 ≠ X0 := superpose step56 step10
  subsumption step81 step56


@[equational_result]
theorem Finite.Equation677_and_Equation108_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step20 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step11
  have step22 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) := superpose step20 step17
  have step24 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose step20 step22
  have step25 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step20 step24
  have step30 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) = X1 := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = X1 := superpose step25 step30
  have step37 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step20 step33
  have step49 (X0 X1 : G) :  X0 = X1 := superpose step37 step20
  have step88 (X0 : G) :  sK0 ≠ X0 := superpose step49 step10
  subsumption step88 step49


@[equational_result]
theorem Finite.Equation677_and_Equation1085_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ Y)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step17 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step12 step13
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step19
  have step40 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step19 step14
  have step53 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step17 step14
  have step110 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step12 step36
  have step113 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step36 step25
  have step128 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step40 step110
  have step145 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step53 step24
  have step171 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step113 step145
  have step179 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step171
  have step186 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step128 step179
  have step195 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step186 step19
  have step220 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step186 step195
  have step253 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1))) := superpose step15 step13
  have step256 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose step220 step253
  have step284 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step220 step256
  have step305 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step220 step284
  have step310 (X0 X1 : G) :  X0 = X1 := superpose step220 step305
  have step367 (X0 : G) :  sK0 ≠ X0 := superpose step310 step11
  subsumption step367 step310


@[equational_result]
theorem Finite.Equation677_and_Equation1110_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ sK1 := mod_symm nh
  have step15 (X Y : G) : (Y ◇ ((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (Y ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step17
  have step52 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step21 step15
  have step57 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step15 step52
  have step73 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step57 step16
  have step74 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose step57 step15
  have step189 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step73 step18
  have step324 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step73 step189
  have step342 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose step189 step17
  have step348 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step74 step342
  have step361 (X0 X1 : G) :  X0 = X1 := superpose step324 step348
  have step441 (X0 : G) :  sK0 ≠ X0 := superpose step361 step13
  subsumption step441 step361


@[equational_result]
theorem Finite.Equation677_and_Equation117_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step23 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step10 step13
  have step32 (X0 X2 : G) :  X0 = X2 := superpose step23 step23
  have step79 (X0 : G) :  sK0 ≠ X0 := superpose step32 step11
  subsumption step79 step32


@[equational_result]
theorem Finite.Equation677_and_Equation1224_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step22 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step9
  have step26 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step22 step17
  have step29 (X0 X1 : G) :  X0 = X1 := superpose step22 step26
  have step44 (X0 : G) :  sK0 ≠ X0 := superpose step29 step10
  subsumption step44 step29


@[equational_result]
theorem Finite.Equation677_and_Equation1225_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step11
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X1 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose step18 step15
  have step23 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step19 step21
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step38 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step23 step32
  have step43 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step19 step38
  have step46 (X0 X1 : G) :  X0 = X1 := superpose step23 step43
  have step64 (X0 : G) :  sK0 ≠ X0 := superpose step46 step10
  subsumption step64 step46


@[equational_result]
theorem Finite.Equation677_and_Equation1228_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step11 step9
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step50 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose step19 step12
  have step54 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step13 step50
  have step94 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step54 step12
  have step97 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step54 step94
  have step122 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step33 step12
  have step125 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step33 step54
  have step137 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step54 step125
  have step139 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step54 step122
  have step156 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step97 step137
  have step158 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step97 step139
  have step172 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step156 step158
  have step184 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step156 step172
  have step190 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step156 step184
  have step212 (X0 X1 : G) :  X0 = X1 := superpose step190 step11
  have step316 (X0 : G) :  sK0 ≠ X0 := superpose step212 step10
  subsumption step316 step212


@[equational_result]
theorem Finite.Equation677_and_Equation1248_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step40 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step19 step9
  have step176 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step40 step20
  have step186 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step20 step12
  have step191 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step40 step176
  have step195 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step191
  have step213 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step195 step12
  have step216 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step195 step213
  have step342 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step216 step11
  have step343 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step216 step342
  have step357 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step216 step343
  have step361 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step216 step357
  have step407 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step16 step11
  have step493 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ X2) ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose step361 step19
  have step505 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step361 step20
  have step506 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step361 step12
  have step507 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step361 step11
  have step723 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0)) := superpose step507 step20
  have step734 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step723
  have step840 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step734 step734
  have step1207 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)))) = X1 := superpose step840 step11
  have step1226 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X1 := superpose step505 step1207
  have step1947 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := superpose step506 step20
  have step2796 (X0 X1 X3 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X3 ◇ X3) ◇ X0)) := superpose step493 step493
  have step3866 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step1947 step12
  have step3873 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X0 := superpose step20 step3866
  have step4116 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X0)) := superpose step3873 step186
  have step4117 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X0)) := superpose step3873 step4116
  have step4156 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step12 step4117
  have step5208 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step4156 step3873
  have step5267 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step19 step5208
  have step5682 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) := superpose step1226 step5267
  have step5708 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step5267 step2796
  have step5709 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose step5267 step493
  have step5710 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step5267 step507
  have step5760 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step5710 step5709
  have step5761 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step5710 step5708
  have step5778 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step5710 step5682
  have step5801 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step5760 step5778
  have step5869 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X1))) := superpose step20 step407
  have step6100 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step12 step5869
  have step6240 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X1)) := superpose step5801 step6100
  have step6367 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step5761 step6240
  have step6474 (X0 X1 : G) :  X0 = X1 := superpose step11 step6367
  have step6800 (X0 : G) :  sK0 ≠ X0 := superpose step6474 step10
  subsumption step6800 step6474


@[equational_result]
theorem Finite.Equation677_and_Equation1252_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step23 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step25 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step37 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step25 step25
  have step38 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step25 step9
  have step273 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X1 := superpose step37 step11
  have step353 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step38 step23
  have step358 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step273 step353
  have step381 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step26 step358
  have step405 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step381 step12
  have step506 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose step25 step405
  have step507 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step405 step9
  have step531 (X0 X1 : G) :  X0 = X1 := superpose step507 step506
  have step637 (X0 : G) :  sK0 ≠ X0 := superpose step531 step10
  subsumption step637 step531


@[equational_result]
theorem Finite.Equation677_and_Equation1276_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((((Y ◇ X) ◇ (Y ◇ X)) ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ s) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose step11 step11
  have step25 (X0 : G) :  ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step16 step11
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step16 step14
  have step37 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step13 step11
  have step73 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step37 step15
  have step87 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose step17 step37
  have step100 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step17 step73
  have step104 (X0 X1 : G) :  ((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step73 step11
  have step112 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step87 step104
  have step113 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step28 step100
  have step147 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose step13 step112
  have step222 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step13 step25
  have step240 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step147 step222
  have step241 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step113 step240
  have step242 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step13 step241
  have step247 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step242 step242
  have step317 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = (((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step28
  have step369 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose step247 step317
  have step405 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step247 step369
  have step486 (X0 X1 : G) :  X0 = X1 := superpose step405 step17
  have step664 (X0 : G) :  sK0 ≠ X0 := superpose step486 step12
  subsumption step664 step486


@[equational_result]
theorem Finite.Equation677_and_Equation1278_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((((Y ◇ X) ◇ (Y ◇ X)) ◇ Y) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ s) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step18 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) = X1 := superpose step13 step10
  have step19 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose step14 step12
  have step124 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step28 step14
  have step126 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose step28 step18
  have step5191 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step124 step14
  have step5565 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step5191 step16
  have step5567 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose step5191 step19
  have step5596 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose step5191 step126
  have step5673 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose step5191 step12
  have step5774 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose step5191 step5596
  have step5795 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ X1) := superpose step5673 step5565
  have step5863 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose step14 step5774
  have step5879 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step5191 step5795
  have step5921 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step5567 step5863
  have step5947 (X0 X1 : G) :  X0 = X1 := superpose step5879 step5921
  have step6483 (X0 : G) :  sK0 ≠ X0 := superpose step5947 step11
  subsumption step6483 step5947


@[equational_result]
theorem Finite.Equation677_and_Equation1427_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step16 step11
  have step26 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step16 step12
  have step29 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step26
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step29
  have step33 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X1 := superpose step11 step17
  have step47 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step30 step33
  have step129 (X0 X1 : G) :  X0 = X1 := superpose step47 step11
  have step185 (X0 : G) :  sK0 ≠ X0 := superpose step129 step10
  subsumption step185 step129


@[equational_result]
theorem Finite.Equation677_and_Equation1428_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step19 step18
  have step30 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose step23 step23
  have step79 (X0 X1 X2 : G) :  (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step30 step12
  have step83 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ X0) := superpose step12 step79
  have step168 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose step83 step11
  have step176 (X0 X1 X2 : G) :  (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose step83 step11
  have step187 (X0 X2 : G) :  X0 = X2 := superpose step176 step168
  have step295 (X0 : G) :  sK0 ≠ X0 := superpose step187 step10
  subsumption step295 step187


@[equational_result]
theorem Finite.Equation677_and_Equation1429_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step17
  have step25 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose step21 step21
  have step84 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step25 step12
  have step93 (X1 X2 : G) :  (X1 ◇ X1) = (X2 ◇ X2) := superpose step12 step84
  have step148 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose step93 step9
  have step157 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step93 step21
  have step180 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose step25 step15
  have step192 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step15 step9
  have step200 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step148 step192
  have step201 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) := superpose step148 step180
  have step206 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose step157 step201
  have step210 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) := superpose step200 step206
  have step213 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose step200 step210
  have step215 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ X1) ◇ X2) := superpose step200 step213
  have step223 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step200 step9
  have step253 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step215 step223
  have step282 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step18 step16
  have step290 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step18 step16
  have step301 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step215 step290
  have step309 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step215 step282
  have step330 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step215 step301
  have step338 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ ((X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step215 step309
  have step356 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose step253 step330
  have step364 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step215 step338
  have step382 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step12 step356
  have step390 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step215 step364
  have step410 (X0 X1 : G) :  (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose step382 step390
  have step424 (X0 X1 : G) :  X0 = X1 := superpose step382 step410
  have step480 (X0 : G) :  sK0 ≠ X0 := superpose step424 step10
  subsumption step480 step424


@[equational_result]
theorem Finite.Equation677_and_Equation1432_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step12
  have step37 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step19 step31
  have step39 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step29 step27
  have step40 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step37
  have step42 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step19 step39
  have step43 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step40 step42
  have step63 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step43 step11
  have step66 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step40 step63
  have step70 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step43 step66
  have step85 (X0 X1 : G) :  X0 = X1 := superpose step70 step11
  have step149 (X0 : G) :  sK0 ≠ X0 := superpose step85 step10
  subsumption step149 step85


@[equational_result]
theorem Finite.Equation677_and_Equation1435_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step10 step14
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step23 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step19 step18
  have step26 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step23 step23
  have step60 (X0 X1 X2 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose step26 step23
  have step229 (X0 X2 : G) :  (X0 ◇ (X0 ◇ X0)) = X2 := superpose step60 step13
  have step257 (X0 X2 : G) :  X0 = X2 := superpose step229 step229
  have step442 (X0 : G) :  sK0 ≠ X0 := superpose step257 step11
  subsumption step442 step257


@[equational_result]
theorem Finite.Equation677_and_Equation1445_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step18 step12
  have step31 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step12 step28
  have step40 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step31 step31
  have step55 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step31 step14
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step31
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step57
  have step71 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step31 step66
  have step102 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step71 step19
  have step126 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step55 step102
  have step132 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step40 step126
  have step134 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step55 step132
  have step136 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step31 step134
  have step149 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step136 step12
  have step156 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step136 step149
  have step165 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step55 step156
  have step169 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step40 step165
  have step269 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step169 step9
  have step282 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step169 step269
  have step305 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = (X0 ◇ ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X1 ◇ X0))) := superpose step11 step15
  have step352 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step282 step305
  have step376 (X0 X1 : G) :  X0 = X1 := superpose step282 step352
  have step442 (X0 : G) :  sK0 ≠ X0 := superpose step376 step10
  subsumption step442 step376


@[equational_result]
theorem Finite.Equation677_and_Equation1478_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step16 step18
  have step33 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step18 step12
  have step36 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step12 step33
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step12 step31
  have step49 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step36 step12
  have step54 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step18
  have step60 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step49 step54
  have step62 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step37 step60
  have step98 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step19 step36
  have step102 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose step19 step9
  have step116 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) = X1 := superpose step62 step102
  have step120 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step18 step98
  have step139 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step62 step116
  have step143 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step62 step120
  have step156 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose step18 step139
  have step160 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ X1) := superpose step62 step143
  have step170 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step62 step156
  have step172 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step62 step160
  have step178 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step62 step170
  have step219 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step178 step19
  have step232 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step178 step219
  have step262 (X0 X1 : G) :  X0 = X1 := superpose step172 step232
  have step339 (X0 : G) :  sK0 ≠ X0 := superpose step262 step10
  subsumption step339 step262


@[equational_result]
theorem Finite.Equation677_and_Equation1488_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step59 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step61 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := superpose step19 step9
  have step62 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose step19 step18
  have step68 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose step18 step61
  have step70 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step18 step59
  have step126 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step15 step9
  have step135 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step126
  have step160 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step135 step9
  have step171 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step70 step160
  have step258 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step171 step135
  have step312 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose step62 step13
  have step332 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step258 step312
  have step357 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step68 step332
  have step382 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step258 step357
  have step402 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step258 step382
  have step476 (X0 X1 : G) :  X0 = X1 := superpose step402 step11
  have step631 (X0 : G) :  sK0 ≠ X0 := superpose step476 step10
  subsumption step631 step476


@[equational_result]
theorem Finite.Equation677_and_Equation1491_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (Y ◇ (X ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ s))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step12 step12
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step10 step10
  have step58 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step13 step16
  have step80 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step10 step58
  have step201 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step16 step15
  have step230 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step80 step201
  have step247 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step12 step230
  have step316 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step247 step14
  have step319 (X0 X1 : G) :  X0 = X1 := superpose step247 step316
  have step444 (X0 : G) :  sK0 ≠ X0 := superpose step319 step11
  subsumption step444 step319


@[equational_result]
theorem Finite.Equation677_and_Equation1515_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ X) ◇ (((Y ◇ Y) ◇ X) ◇ ((Y ◇ Y) ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step10 step14
  have step43 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step12
  have step148 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step12 step43
  have step169 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step18 step148
  have step181 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step148 step13
  have step185 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step148 step10
  have step187 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step148 step14
  have step198 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step148 step187
  have step201 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step185 step169
  have step207 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step181 step198
  have step208 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step185 step201
  have step211 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step207 step208
  have step213 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step207 step211
  have step214 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step207 step213
  have step215 (X0 X1 : G) :  X0 = X1 := superpose step207 step214
  have step264 (X0 : G) :  sK0 ≠ X0 := superpose step215 step11
  subsumption step264 step215


@[equational_result]
theorem Finite.Equation677_and_Equation1518_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ X) ◇ (Y ◇ ((Y ◇ Y) ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step10 step10
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step16 step13
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step10
  have step25 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step24
  have step26 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step10 step14
  have step32 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step14
  have step35 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step25 step32
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step35
  have step61 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step12 step14
  have step66 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step39 step61
  have step111 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step26 step14
  have step119 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step14 step111
  have step133 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step39 step119
  have step162 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step13 step133
  have step194 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step133 step66
  have step207 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step162 step194
  have step223 (X0 X1 : G) :  X0 = X1 := superpose step162 step207
  have step271 (X0 : G) :  sK0 ≠ X0 := superpose step223 step11
  subsumption step271 step223


@[equational_result]
theorem Finite.Equation677_and_Equation1631_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step17
  have step24 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose step16 step16
  have step31 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step12
  have step34 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step31
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step19 step16
  have step41 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step34 step36
  have step46 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose step24 step12
  have step49 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step12 step46
  have step57 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := superpose step23 step11
  have step59 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose step23 step12
  have step69 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step23 step12
  have step74 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) = X0 := superpose step49 step69
  have step77 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step41 step59
  have step78 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose step41 step57
  have step79 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step23 step74
  have step82 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step49 step77
  have step83 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step49 step78
  have step84 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step41 step79
  have step85 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose step49 step84
  have step86 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step82 step85
  have step99 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose step86 step9
  have step129 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step83 step99
  have step171 (X0 X1 : G) :  X0 = X1 := superpose step129 step11
  have step252 (X0 : G) :  sK0 ≠ X0 := superpose step171 step10
  subsumption step252 step171


@[equational_result]
theorem Finite.Equation677_and_Equation1634_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step17
  have step30 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose step23 step23
  have step37 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := superpose step23 step12
  have step72 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose step30 step11
  have step73 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose step30 step19
  have step105 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) := superpose step72 step30
  have step106 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose step72 step105
  have step272 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step73 step15
  have step297 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step37 step272
  have step314 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step297 step72
  have step329 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step314
  have step361 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step13 step30
  have step365 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose step106 step361
  have step439 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step329 step13
  have step440 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step365 step439
  have step595 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step18 step440
  have step617 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step440 step12
  have step637 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step440 step617
  have step648 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step440 step595
  have step666 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step637 step648
  have step857 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step666 step12
  have step874 (X0 X1 : G) :  X0 = X1 := superpose step666 step857
  have step1072 (X0 : G) :  sK0 ≠ X0 := superpose step874 step10
  subsumption step1072 step874


@[equational_result]
theorem Finite.Equation677_and_Equation1635_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step17
  have step31 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := superpose step23 step23
  have step62 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X2 ◇ X1) ◇ X2) := superpose step23 step31
  have step80 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose step31 step12
  have step82 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose step31 step19
  have step87 (X1 X2 : G) :  ((X2 ◇ X1) ◇ X2) = X1 := superpose step82 step62
  have step167 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step172 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step80 step167
  have step204 (X0 X1 : G) :  X0 = X1 := superpose step87 step172
  have step270 (X0 : G) :  sK0 ≠ X0 := superpose step204 step10
  subsumption step270 step204


@[equational_result]
theorem Finite.Equation677_and_Equation1637_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = (((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0) := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step32 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step25 step25
  have step35 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step25 step11
  have step78 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = X2 := superpose step32 step9
  have step80 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step32 step11
  have step117 (X0 X1 X2 X3 : G) :  ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3)) = X3 := superpose step32 step78
  have step205 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step80 step78
  have step234 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step21 step20
  have step265 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step234
  have step430 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step205 step12
  have step433 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step117 step430
  have step595 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step433 step12
  have step1196 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step25
  have step1548 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step265 step12
  have step1550 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step595 step1548
  have step1759 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose step32 step1550
  have step1768 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step1550 step12
  have step1771 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step78 step1768
  have step1778 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step1759 step1771
  have step1895 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step1778 step78
  have step1900 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step1778 step1550
  have step1924 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step1900 step1895
  have step2018 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)))) = X0 := superpose step1196 step35
  have step2042 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2))) = X0 := superpose step1924 step2018
  have step2094 (X0 X1 X2 : G) :  ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := superpose step1924 step2042
  have step2134 (X0 X2 : G) :  (X2 ◇ X2) = X0 := superpose step1924 step2094
  have step2155 (X0 X2 : G) :  X0 = X2 := superpose step1924 step2134
  have step2314 (X0 : G) :  sK0 ≠ X0 := superpose step2155 step10
  subsumption step2314 step2155


@[equational_result]
theorem Finite.Equation677_and_Equation1638_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((X ◇ ((Y ◇ Y) ◇ Y)) ◇ (X ◇ ((Y ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step10 step13
  have step31 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step19 step10
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step10
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step19 step33
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step31 step36
  have step42 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step19 step12
  have step56 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step38 step42
  have step63 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step38 step56
  have step103 (X0 X1 : G) :  X0 = X1 := superpose step63 step13
  have step149 (X0 : G) :  sK0 ≠ X0 := superpose step103 step11
  subsumption step149 step103


@[equational_result]
theorem Finite.Equation677_and_Equation1644_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose step11 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step20
  have step25 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose step16 step16
  have step26 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step11
  have step34 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step16 step12
  have step35 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step23 step34
  have step40 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step26 step25
  have step42 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step26 step35
  have step47 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step26 step40
  have step49 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step26 step42
  have step55 (X0 X1 : G) :  X0 = X1 := superpose step47 step49
  have step86 (X0 : G) :  sK0 ≠ X0 := superpose step55 step10
  subsumption step86 step55


@[equational_result]
theorem Finite.Equation677_and_Equation1645_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step28 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose step14 step11
  have step30 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step11 step28
  have step62 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step30 step12
  have step66 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step62
  have step68 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step66
  have step125 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X0 := superpose step68 step18
  have step135 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step11 step125
  have step212 (X0 X1 : G) :  X0 = X1 := superpose step135 step68
  have step363 (X0 : G) :  sK0 ≠ X0 := superpose step212 step10
  subsumption step363 step212


@[equational_result]
theorem Finite.Equation677_and_Equation1684_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step119 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step20 step14
  have step122 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step20 step9
  have step123 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose step20 step9
  have step126 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step20 step12
  have step131 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) := superpose step20 step19
  have step132 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step20 step19
  have step144 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) ◇ X1)) := superpose step132 step131
  have step149 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step19 step126
  have step152 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose step19 step123
  have step153 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step19 step122
  have step155 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step19 step119
  have step161 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1)) := superpose step19 step144
  have step163 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step153 step155
  have step168 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X1) := superpose step132 step132
  have step180 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step132
  have step184 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose step132 step11
  have step187 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step132 step19
  have step219 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step132 step180
  have step309 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step219 step11
  have step310 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step219 step9
  have step319 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step219 step14
  have step326 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step219 step20
  have step329 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step132 step326
  have step333 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step132 step319
  have step339 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step168 step329
  have step342 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step168 step333
  have step346 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step21 step339
  have step348 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step21 step342
  have step349 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step310 step346
  have step351 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step309 step348
  have step377 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step21 step16
  have step418 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step149 step377
  have step438 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step349 step418
  have step480 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step351 step132
  have step481 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step219 step480
  have step498 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step349 step481
  have step514 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step438 step498
  have step1697 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step132 step153
  have step1699 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step132 step153
  have step1714 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose step11 step153
  have step1730 (X0 X1 : G) :  (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step132 step153
  have step1752 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step153 step19
  have step1779 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step153 step1752
  have step1806 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X1) ◇ (X0 ◇ X1)) := superpose step132 step1714
  have step1862 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose step11 step1806
  have step2092 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step132 step163
  have step2124 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step163 step132
  have step2729 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step184 step12
  have step5533 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step187 step163
  have step7220 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))))) := superpose step1697 step15
  have step7275 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step1730 step7220
  have step7406 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step1862 step7275
  have step7487 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step514 step7406
  have step7550 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step2092 step7487
  have step7672 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step9 step161
  have step7706 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose step163 step161
  have step7738 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step161 step163
  have step7830 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step7550 step7738
  have step7853 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose step2729 step7706
  have step7884 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step2729 step7672
  have step7930 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose step152 step7830
  have step7950 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step7550 step7853
  have step7980 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step7550 step7884
  have step8008 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose step7550 step7930
  have step8024 (X0 X1 : G) :  ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step132 step7950
  have step8051 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step5533 step7980
  have step8079 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step8008 step8024
  have step8104 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step8008 step8051
  have step8126 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step2124 step8079
  have step8148 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) := superpose step132 step8104
  have step8163 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step7550 step8126
  have step8183 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step1862 step8148
  have step8194 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step8008 step8163
  have step8209 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step7550 step8183
  have step8218 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step163 step8194
  have step8228 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step219 step8209
  have step8233 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X1 := superpose step8008 step8218
  have step8242 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step349 step8228
  have step8250 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step514 step8242
  have step8291 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step184 step8008
  have step8332 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X0)) := superpose step8008 step16
  have step8397 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step1779 step8332
  have step8433 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step163 step8291
  have step8498 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step8233 step8397
  have step8524 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step8250 step8433
  have step8576 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step8250 step8498
  have step8591 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step8250 step8524
  have step8636 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step8576 step8591
  have step9073 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose step8636 step1699
  have step9197 (X0 X1 : G) :  X0 = X1 := superpose step8636 step9073
  have step9615 (X0 : G) :  sK0 ≠ X0 := superpose step9197 step10
  subsumption step9615 step9197


@[equational_result]
theorem Finite.Equation677_and_Equation1692_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (Y ◇ (X ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (s ◇ Y))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step10 step10
  have step28 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step10
  have step101 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step13 step19
  have step139 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose step10 step101
  have step145 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step139 step139
  have step155 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step139 step10
  have step169 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step155 step145
  have step192 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose step28 step12
  have step197 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step28 step19
  have step201 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step169 step197
  have step206 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose step169 step192
  have step221 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step139 step201
  have step224 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step139 step206
  have step233 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step139 step221
  have step240 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step224 step233
  have step269 (X0 X1 : G) :  X0 = X1 := superpose step240 step13
  have step363 (X0 : G) :  sK0 ≠ X0 := superpose step269 step11
  subsumption step363 step269


@[equational_result]
theorem Finite.Equation677_and_Equation1694_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step9 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step31 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step14 step12
  have step34 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step20 step31
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step34
  have step41 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step35 step9
  have step44 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step35 step41
  have step54 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose step12 step19
  have step74 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose step44 step54
  have step84 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step44 step74
  have step91 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step44 step84
  have step95 (X0 X1 : G) :  X0 = X1 := superpose step44 step91
  have step123 (X0 : G) :  sK0 ≠ X0 := superpose step95 step10
  subsumption step123 step95


@[equational_result]
theorem Finite.Equation677_and_Equation1719_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ ((Y ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((((Y ◇ Y) ◇ X) ◇ ((Y ◇ Y) ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((s ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose step11 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step11 step11
  have step54 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step13
  have step69 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step54 step16
  have step71 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose step54 step14
  have step74 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step71
  have step75 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step69
  have step88 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X1 ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1))) := superpose step17 step15
  have step92 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step74 step88
  have step99 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose step75 step92
  have step106 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step75 step99
  have step113 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step75 step106
  have step117 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose step75 step11
  have step155 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X1 := superpose step113 step117
  have step161 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step75 step155
  have step203 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X2 := superpose step18 step17
  have step217 (X1 X2 : G) :  (X1 ◇ X1) = X2 := superpose step161 step203
  have step247 (X1 X2 : G) :  X1 = X2 := superpose step161 step217
  have step313 (X0 : G) :  sK0 ≠ X0 := superpose step247 step12
  subsumption step313 step247


@[equational_result]
theorem Finite.Equation677_and_Equation1721_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((((Y ◇ Y) ◇ X) ◇ Y) ◇ ((Y ◇ Y) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((s ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step10 step13
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step12
  have step31 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step13
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step31 step13
  have step46 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step31 step10
  have step58 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step29 step14
  have step60 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step29 step10
  have step61 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step60
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step46 step58
  have step66 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step46 step61
  have step67 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step20 step63
  have step69 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step66 step67
  have step70 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step66 step69
  have step79 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step70 step10
  have step80 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step66 step79
  have step85 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step45 step80
  have step136 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step85 step31
  have step150 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step85 step136
  have step197 (X0 X1 : G) :  X0 = X1 := superpose step150 step13
  have step321 (X0 : G) :  sK0 ≠ X0 := superpose step197 step11
  subsumption step321 step197


@[equational_result]
theorem Finite.Equation677_and_Equation1833_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step18 step16
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step19 step21
  have step31 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step19 step27
  have step34 (X0 X1 : G) :  X0 = X1 := superpose step19 step31
  have step48 (X0 : G) :  sK0 ≠ X0 := superpose step34 step10
  subsumption step48 step34


@[equational_result]
theorem Finite.Equation677_and_Equation1834_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step9
  have step31 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step20
  have step35 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step31
  have step38 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step16 step35
  have step40 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step25 step38
  have step41 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step25 step40
  have step64 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step41 step12
  have step65 (X0 X1 : G) :  X0 = X1 := superpose step41 step64
  have step92 (X0 : G) :  sK0 ≠ X0 := superpose step65 step10
  subsumption step92 step65


@[equational_result]
theorem Finite.Equation677_and_Equation1837_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step17 step20
  have step30 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step23 step12
  have step34 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step30
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step34
  have step47 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step11 step17
  have step67 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step35 step47
  have step95 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step67 step12
  have step96 (X0 X1 : G) :  X0 = X1 := superpose step67 step95
  have step152 (X0 : G) :  sK0 ≠ X0 := superpose step96 step10
  subsumption step152 step96


@[equational_result]
theorem Finite.Equation677_and_Equation1847_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step19
  have step23 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step11
  have step24 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step22 step12
  have step27 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step18 step24
  have step28 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step27
  have step43 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step28 step9
  have step56 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step17 step12
  have step61 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step12 step56
  have step71 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step43 step61
  have step241 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step71 step12
  have step254 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step9 step241
  have step305 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step18 step15
  have step353 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step254 step305
  have step390 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step254 step353
  have step422 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step390
  have step449 (X0 X1 : G) :  X0 = X1 := superpose step254 step422
  have step519 (X0 : G) :  sK0 ≠ X0 := superpose step449 step10
  subsumption step519 step449


@[equational_result]
theorem Finite.Equation677_and_Equation1857_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step9
  have step32 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step14 step12
  have step34 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step12 step32
  have step37 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step34
  have step52 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step18 step12
  have step54 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step12 step52
  have step59 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := superpose step9 step54
  have step111 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step37 step34
  have step250 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step59 step34
  have step260 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step34 step250
  have step347 (X0 X1 X2 : G) :  ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X1 := superpose step260 step9
  have step369 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step260 step19
  have step371 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step260 step11
  have step376 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := superpose step260 step14
  have step378 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step260 step15
  have step379 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step111 step378
  have step409 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step260 step21
  have step417 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step54 step409
  have step637 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0)) := superpose step371 step19
  have step640 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose step12 step637
  have step822 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose step376 step12
  have step924 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step417 step822
  have step1592 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step23 step17
  have step1599 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step369 step1592
  have step1609 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step417 step1599
  have step1612 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step640 step1609
  have step1614 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step37 step1612
  have step1615 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step924 step1614
  have step1616 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step11 step1615
  have step1617 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step640 step1616
  have step1640 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step1617 step20
  have step1668 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step379 step1640
  have step1809 (X0 X1 X2 : G) :  ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X1 := superpose step1668 step347
  have step1841 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose step1668 step34
  have step1852 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step1668 step1841
  have step1863 (X0 X1 X2 : G) :  ((X1 ◇ X0) ◇ X2) = X1 := superpose step1668 step1809
  have step1875 (X1 X2 : G) :  X1 = X2 := superpose step1852 step1863
  have step2074 (X0 : G) :  sK0 ≠ X0 := superpose step1875 step10
  subsumption step2074 step1875


@[equational_result]
theorem Finite.Equation677_and_Equation1858_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step13 step12
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step23
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step26 step12
  have step51 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step32 step18
  have step55 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step32 step20
  have step57 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step32 step9
  have step62 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step57 step55
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step51
  have step73 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step26 step19
  have step90 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step19 step73
  have step99 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step62 step90
  have step102 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step63 step99
  have step105 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step63 step102
  have step108 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step105 step9
  have step126 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step105 step108
  have step217 (X0 X1 : G) :  X0 = X1 := superpose step126 step11
  have step346 (X0 : G) :  sK0 ≠ X0 := superpose step217 step10
  subsumption step346 step217


@[equational_result]
theorem Finite.Equation677_and_Equation1876_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 X3 : G) :  ((X1 ◇ X0) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3)))) = X1 := superpose step9 step9
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose step11 step9
  have step19 (X0 X1 X2 : G) :  ((X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2)) ◇ X0) = X1 := superpose step11 step9
  have step24 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step12 step9
  have step49 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step24 step12
  have step55 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step49
  have step61 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step55 step18
  have step67 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step17 step61
  have step127 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step67 step9
  have step136 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step67 step9
  have step283 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose step17 step127
  have step284 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step136 step283
  have step315 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step67 step284
  have step406 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step315 step24
  have step415 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step315 step127
  have step429 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step415 step406
  have step450 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step415 step429
  have step504 (X0 X1 X2 X3 X4 : G) :  ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X3) ◇ X4)) ◇ X4))) ◇ (X2 ◇ X0))) = X1 := superpose step19 step13
  have step531 (X0 X1 X2 X3 X4 : G) :  ((X3 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X3) ◇ X4)) ◇ X4))) ◇ (X2 ◇ X0)) = X1 := superpose step450 step504
  have step575 (X0 X1 X2 : G) :  (X2 ◇ X0) = X1 := superpose step450 step531
  have step676 (X0 X1 : G) :  X0 = X1 := superpose step575 step13
  have step877 (X0 : G) :  sK0 ≠ X0 := superpose step676 step10
  subsumption step877 step676


@[equational_result]
theorem Finite.Equation677_and_Equation1884_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ X) ◇ ((Y ◇ X) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ s)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step10
  have step26 (X0 X1 X2 : G) :  ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose step12 step10
  have step28 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step10 step14
  have step30 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step15 step14
  have step39 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step32 step10
  have step75 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose step26 step13
  have step83 (X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose step39 step75
  have step99 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step15 step83
  have step117 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step99 step12
  have step175 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step117 step14
  have step178 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step39 step175
  have step184 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step99 step178
  have step272 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step28 step117
  have step273 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step99 step272
  have step285 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step39 step273
  have step294 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step99 step285
  have step302 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step184 step294
  have step342 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step302 step117
  have step343 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step302 step342
  have step361 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step117 step30
  have step436 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step184 step361
  have step465 (X0 X1 : G) :  X0 = X1 := superpose step343 step436
  have step534 (X0 : G) :  sK0 ≠ X0 := superpose step465 step11
  subsumption step534 step465


@[equational_result]
theorem Finite.Equation677_and_Equation1887_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step26 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose step20 step9
  have step75 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step26 step11
  have step126 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step75 step20
  have step145 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step126
  have step248 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose step145 step9
  have step282 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step145 step248
  have step312 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step19 step16
  have step366 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step282 step312
  have step408 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step282 step366
  have step447 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step408
  have step481 (X0 X1 : G) :  X0 = X1 := superpose step282 step447
  have step567 (X0 : G) :  sK0 ≠ X0 := superpose step481 step10
  subsumption step567 step481


@[equational_result]
theorem Finite.Equation677_and_Equation1888_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ Y)) ◇ ((Y ◇ X) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ (Y ◇ Y)) ◇ (X ◇ (Y ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (Y ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step11 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose step11 step15
  have step21 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step15 step15
  have step22 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step11 step16
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step16 step15
  have step28 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step14 step16
  have step36 (X0 X1 X2 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose step13 step14
  have step37 (X0 X1 X2 : G) :  ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose step13 step11
  have step70 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X2 := superpose step17 step11
  have step283 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose step24 step37
  have step529 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step24 step22
  have step557 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step23 step529
  have step1456 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step283 step22
  have step1485 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step1456
  have step1560 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step20
  have step1575 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step1485 step1560
  have step1589 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step1575
  have step1591 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step557 step1589
  have step1592 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step1485 step1591
  have step1593 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step1485 step1592
  have step1594 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step1593
  have step1604 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step28 step1594
  have step1633 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose step1594 step70
  have step1644 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step1594 step11
  have step1707 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step1644 step1633
  have step1724 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step1644 step1604
  have step1742 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X0 := superpose step1707 step1724
  have step1749 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step1644 step1742
  have step1794 (X0 X1 X2 : G) :  (X0 ◇ X1) = (((X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step25 step36
  have step1805 (X0 X1 X2 : G) :  (X0 ◇ X1) = ((X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X2)) := superpose step1749 step1794
  have step1848 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step1749 step1805
  have step1865 (X0 X1 X2 : G) :  (X0 ◇ X1) = X2 := superpose step1749 step1848
  have step2018 (X0 X3 : G) :  X0 = X3 := superpose step1865 step37
  have step2403 (X0 : G) :  sK0 ≠ X0 := superpose step2018 step12
  subsumption step2403 step2018


@[equational_result]
theorem Finite.Equation677_and_Equation1894_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step11
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step16
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step9 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step18 step12
  have step44 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step25 step11
  have step47 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step25 step18
  have step49 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step18 step44
  have step51 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step47 step49
  have step52 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step51
  have step83 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose step52 step9
  have step91 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step19
  have step104 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step19 step12
  have step109 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step83 step104
  have step118 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step47 step91
  have step122 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step12 step109
  have step129 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step52 step118
  have step136 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step122 step129
  have step142 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step52 step136
  have step145 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step9 step142
  have step165 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step145 step11
  have step168 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step52 step165
  have step179 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step145 step168
  have step283 (X0 X1 : G) :  X0 = X1 := superpose step179 step11
  have step405 (X0 : G) :  sK0 ≠ X0 := superpose step283 step10
  subsumption step405 step283


@[equational_result]
theorem Finite.Equation677_and_Equation1925_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ (Y ◇ (X ◇ (Y ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (Y ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step13 step13
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step15 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step13
  have step65 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step26 step15
  have step72 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step13 step65
  have step75 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step19 step72
  have step80 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step75 step14
  have step123 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step80 step11
  have step149 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step80 step19
  have step244 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step123 step16
  have step291 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose step13 step27
  have step334 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose step244 step291
  have step357 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose step80 step334
  have step377 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step149 step357
  have step392 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X1) := superpose step244 step377
  have step401 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step80 step392
  have step458 (X0 X1 : G) :  X0 = X1 := superpose step401 step123
  have step577 (X0 : G) :  sK0 ≠ X0 := superpose step458 step12
  subsumption step577 step458


@[equational_result]
theorem Finite.Equation677_and_Equation1931_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ (Y ◇ Y)) ◇ X) ◇ ((Y ◇ (Y ◇ Y)) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose step10 step13
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step10 step14
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step23 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step10 step14
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step14 step12
  have step260 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step19 step14
  have step270 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose step14 step260
  have step284 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose step10 step270
  have step344 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step31 step20
  have step373 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step284 step344
  have step385 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step23 step373
  have step387 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step284 step385
  have step388 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step387
  have step419 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose step388 step12
  have step420 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step388 step419
  have step445 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step388 step420
  have step474 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step388 step16
  have step525 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step445 step474
  have step550 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose step445 step525
  have step565 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step445 step550
  have step579 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step445 step565
  have step590 (X0 X1 : G) :  X0 = X1 := superpose step445 step579
  have step668 (X0 : G) :  sK0 ≠ X0 := superpose step590 step11
  subsumption step668 step590


@[equational_result]
theorem Finite.Equation677_and_Equation2036_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step11
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step17 step14
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step18 step20
  have step30 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step18 step26
  have step33 (X0 X1 : G) :  X0 = X1 := superpose step18 step30
  have step47 (X0 : G) :  sK0 ≠ X0 := superpose step33 step10
  subsumption step47 step33


@[equational_result]
theorem Finite.Equation677_and_Equation2037_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step30 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step22 step21
  have step32 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step18 step30
  have step33 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step18 step32
  have step34 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step17 step33
  have step46 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step34 step12
  have step53 (X0 X1 : G) :  X0 = X1 := superpose step34 step46
  have step89 (X0 : G) :  sK0 ≠ X0 := superpose step53 step10
  subsumption step89 step53


@[equational_result]
theorem Finite.Equation677_and_Equation2038_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step13
  have step24 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step17 step10
  have step51 (X0 X1 : G) :  X0 = X1 := superpose step24 step13
  have step138 (X0 : G) :  sK0 ≠ X0 := superpose step51 step11
  subsumption step138 step51


@[equational_result]
theorem Finite.Equation677_and_Equation2040_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step13 step10
  have step26 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step19 step19
  have step40 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step19 step14
  have step45 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step26 step40
  have step66 (X0 X1 : G) :  X0 = X1 := superpose step45 step19
  have step132 (X0 : G) :  sK0 ≠ X0 := superpose step66 step11
  subsumption step132 step66


@[equational_result]
theorem Finite.Equation677_and_Equation2041_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = X1 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step17 step9
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step9
  have step68 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step30 step12
  have step72 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step21 step68
  have step73 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step72
  have step74 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) ◇ X1) := superpose step17 step18
  have step110 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X0 := superpose step73 step74
  have step123 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step11 step110
  have step153 (X0 X1 : G) :  X0 = X1 := superpose step123 step17
  have step279 (X0 : G) :  sK0 ≠ X0 := superpose step153 step10
  subsumption step279 step153


@[equational_result]
theorem Finite.Equation677_and_Equation2050_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step28 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step18
  have step31 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step18 step12
  have step53 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step21 step28
  have step62 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step53 step12
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step62
  have step98 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step20
  have step101 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step18 step20
  have step121 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1) := superpose step20 step28
  have step129 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step31 step121
  have step140 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose step12 step101
  have step142 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step18 step98
  have step149 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step66 step142
  have step151 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step140 step149
  have step152 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step129 step151
  have step164 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step152 step28
  have step235 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step20 step164
  have step262 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step31 step235
  have step268 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step152 step262
  have step290 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step20 step16
  have step338 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step268 step290
  have step375 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step268 step338
  have step409 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step375
  have step439 (X0 X1 : G) :  X0 = X1 := superpose step268 step409
  have step520 (X0 : G) :  sK0 ≠ X0 := superpose step439 step10
  subsumption step520 step439


@[equational_result]
theorem Finite.Equation677_and_Equation2087_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step11
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step13 step12
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step19 step30
  have step35 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step16 step34
  have step50 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step35 step12
  have step55 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step35 step50
  have step66 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step18 step12
  have step69 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step12 step66
  have step84 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step55 step12
  have step86 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step55 step12
  have step91 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step86 step84
  have step94 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step91
  have step108 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step35 step19
  have step125 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step94 step108
  have step133 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step69 step125
  have step136 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step133 step11
  have step179 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step14 step12
  have step184 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step136 step179
  have step201 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step18 step184
  have step208 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step136 step201
  have step540 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose step208 step19
  have step545 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step540
  have step566 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose step136 step545
  have step583 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step136 step566
  have step701 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step19 step583
  have step714 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step583 step12
  have step736 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step583 step714
  have step741 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step583 step701
  have step756 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step736 step741
  have step936 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step756 step12
  have step956 (X0 X1 : G) :  X0 = X1 := superpose step756 step936
  have step1140 (X0 : G) :  sK0 ≠ X0 := superpose step956 step10
  subsumption step1140 step956


@[equational_result]
theorem Finite.Equation677_and_Equation2097_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step9
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step19 step11
  have step23 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step19 step14
  have step25 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step21
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step23 step25
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step19 step26
  have step28 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step9 step12
  have step40 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step27 step28
  have step48 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose step27 step9
  have step63 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step40 step11
  have step66 (X0 X1 : G) :  (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step9 step63
  have step76 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step48 step66
  have step82 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step27 step76
  have step168 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step82 step82
  have step181 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step82 step12
  have step188 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step9 step168
  have step197 (X0 X1 : G) :  X0 = X1 := superpose step181 step188
  have step284 (X0 : G) :  sK0 ≠ X0 := superpose step197 step10
  subsumption step284 step197


@[equational_result]
theorem Finite.Equation677_and_Equation211_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose step9 step11
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step19
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step20 step22
  have step32 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step24 step9
  have step56 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) := superpose step11 step16
  have step66 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step32 step56
  have step81 (X0 X1 : G) :  X0 = X1 := superpose step66 step24
  have step154 (X0 : G) :  sK0 ≠ X0 := superpose step81 step10
  subsumption step154 step81


@[equational_result]
theorem Finite.Equation677_and_Equation2124_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step17 step9
  have step46 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step25 step12
  have step95 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) = X1 := superpose step20 step25
  have step107 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step46 step95
  have step119 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step17 step107
  have step137 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step107 step20
  have step141 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose step12 step137
  have step146 (X0 X1 : G) :  X0 = X1 := superpose step119 step141
  have step219 (X0 : G) :  sK0 ≠ X0 := superpose step146 step10
  subsumption step219 step146


@[equational_result]
theorem Finite.Equation677_and_Equation2127_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step9
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step26 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step17 step9
  have step39 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step26 step12
  have step41 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step26 step9
  have step42 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step26 step9
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step42
  have step44 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step39
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step43
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step54 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step41 step49
  have step60 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step44 step54
  have step65 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step45 step60
  have step72 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step65 step9
  have step81 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step65 step72
  have step171 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step81 step12
  have step173 (X0 X1 : G) :  X0 = X1 := superpose step81 step171
  have step266 (X0 : G) :  sK0 ≠ X0 := superpose step173 step10
  subsumption step266 step173


@[equational_result]
theorem Finite.Equation677_and_Equation2128_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ Y) ◇ (X ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step20 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose step10 step13
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step10
  have step30 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step20 step12
  have step32 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step20 step10
  have step34 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step32 step30
  have step123 (X0 X1 : G) :  X0 = X1 := superpose step34 step27
  have step212 (X0 : G) :  sK0 ≠ X0 := superpose step123 step11
  subsumption step212 step123


@[equational_result]
theorem Finite.Equation677_and_Equation2134_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((((Y ◇ Y) ◇ Y) ◇ X) ◇ (((Y ◇ Y) ◇ Y) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step13
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step10 step14
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step23 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose step17 step10
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step14 step12
  have step41 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose step17 step23
  have step290 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step10 step18
  have step326 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step17 step290
  have step373 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step326 step14
  have step375 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step19 step373
  have step377 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := superpose step41 step375
  have step390 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step31 step19
  have step450 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step377 step390
  have step470 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step10 step450
  have step478 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step377 step470
  have step480 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step17 step478
  have step493 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step480 step18
  have step511 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := superpose step480 step12
  have step525 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step480 step511
  have step540 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step480 step493
  have step548 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step480 step525
  have step561 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step480 step540
  have step573 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step548 step561
  have step574 (X0 X1 : G) :  X0 = X1 := superpose step548 step573
  have step698 (X0 : G) :  sK0 ≠ X0 := superpose step574 step11
  subsumption step698 step574


@[equational_result]
theorem Finite.Equation677_and_Equation221_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step20
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step18
  have step26 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step24
  have step57 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step25
  have step76 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step26 step57
  have step80 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step9 step76
  have step81 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step9 step80
  have step95 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step81 step11
  have step97 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step26 step95
  have step105 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step81 step97
  have step165 (X0 X1 : G) :  X0 = X1 := superpose step105 step11
  have step250 (X0 : G) :  sK0 ≠ X0 := superpose step165 step10
  subsumption step250 step165


@[equational_result]
theorem Finite.Equation677_and_Equation2240_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step11 step9
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step9 step12
  have step32 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step20 step28
  have step34 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step20 step26
  have step36 (X0 X1 : G) :  X0 = X1 := superpose step32 step34
  have step50 (X0 : G) :  sK0 ≠ X0 := superpose step36 step10
  subsumption step50 step36


@[equational_result]
theorem Finite.Equation677_and_Equation2243_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step34 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step12
  have step39 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose step9 step12
  have step47 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step34
  have step59 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step39 step11
  have step64 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step20 step59
  have step77 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step47 step12
  have step86 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose step20 step77
  have step96 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose step64 step86
  have step105 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step9 step96
  have step130 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step105 step39
  have step144 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step20 step130
  have step235 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step144 step12
  have step236 (X0 X1 : G) :  X0 = X1 := superpose step144 step235
  have step331 (X0 : G) :  sK0 ≠ X0 := superpose step236 step10
  subsumption step331 step236


@[equational_result]
theorem Finite.Equation677_and_Equation2246_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step18
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step9
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step21 step9
  have step34 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step21 step30
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step28 step27
  have step37 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)))) := superpose step9 step23
  have step47 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step9 step37
  have step52 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose step9 step47
  have step54 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step9 step52
  have step56 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step34 step54
  have step57 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step35 step56
  have step58 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step35 step57
  have step95 (X0 X1 : G) :  X0 = X1 := superpose step58 step11
  have step160 (X0 : G) :  sK0 ≠ X0 := superpose step95 step10
  subsumption step160 step95


@[equational_result]
theorem Finite.Equation677_and_Equation2253_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step11
  have step22 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step27
  have step34 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step22
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose step30 step34
  have step88 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := superpose step18 step11
  have step89 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose step30 step88
  have step93 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose step18 step89
  have step94 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step30 step93
  have step118 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step37 step24
  have step144 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step12 step118
  have step163 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step94 step144
  have step173 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step30 step163
  have step202 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step173 step12
  have step205 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step173 step202
  have step296 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step205 step12
  have step303 (X0 X1 : G) :  X0 = X1 := superpose step205 step296
  have step427 (X0 : G) :  sK0 ≠ X0 := superpose step303 step10
  subsumption step427 step303


@[equational_result]
theorem Finite.Equation677_and_Equation2256_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X1) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step18
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step12
  have step69 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step21 step17
  have step94 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step69
  have step97 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step21 step94
  have step111 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step25 step20
  have step126 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step97 step111
  have step127 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step126
  have step133 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step127 step21
  have step137 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step127 step12
  have step142 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step137
  have step166 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)) := superpose step24 step19
  have step193 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X0) := superpose step12 step166
  have step201 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ X0) := superpose step133 step193
  have step208 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step142 step201
  have step509 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step208 step12
  have step523 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step133 step509
  have step542 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose step142 step523
  have step551 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step142 step542
  have step705 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step551 step12
  have step714 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step551 step208
  have step721 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step714 step705
  have step869 (X0 X1 : G) :  X0 = X1 := superpose step721 step11
  have step1081 (X0 : G) :  sK0 ≠ X0 := superpose step869 step10
  subsumption step1081 step869


@[equational_result]
theorem Finite.Equation677_and_Equation2266_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step17
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step20 step12
  have step52 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step16 step16
  have step62 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step52
  have step85 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose step62 step20
  have step112 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step20 step18
  have step119 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ X0)) := superpose step22 step18
  have step140 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ X0) := superpose step12 step119
  have step144 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step18 step112
  have step148 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step85 step144
  have step150 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step23 step148
  have step151 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step150
  have step152 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step140 step151
  have step153 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step23 step152
  have step163 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step152 step12
  have step166 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step152 step163
  have step173 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step153 step166
  have step213 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose step173 step9
  have step215 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step173 step16
  have step238 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step173 step215
  have step240 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step173 step213
  have step282 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step62 step15
  have step284 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step15 step18
  have step291 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose step12 step284
  have step292 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) := superpose step238 step282
  have step326 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step240 step291
  have step327 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = ((X1 ◇ X1) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) := superpose step18 step292
  have step352 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) := superpose step326 step327
  have step368 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X1) = X0 := superpose step326 step352
  have step379 (X0 X1 : G) :  X0 = X1 := superpose step240 step368
  have step446 (X0 : G) :  sK0 ≠ X0 := superpose step379 step10
  subsumption step446 step379


@[equational_result]
theorem Finite.Equation677_and_Equation2290_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step11
  have step19 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step11
  have step20 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step18
  have step22 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step20 step9
  have step24 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step30
  have step38 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose step20 step24
  have step41 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step33 step38
  have step55 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) := superpose step11 step41
  have step59 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step41 step11
  have step60 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step41 step12
  have step63 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step19 step60
  have step67 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step12 step55
  have step71 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step59 step63
  have step73 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step33 step71
  have step100 (X0 X1 : G) :  ((X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) ◇ X1) = X1 := superpose step26 step9
  have step115 (X0 X1 : G) :  (((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1) = X1 := superpose step67 step100
  have step130 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step73 step115
  have step145 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step59 step130
  have step155 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step73 step145
  have step178 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step155 step11
  have step202 (X0 X1 : G) :  X0 = X1 := superpose step73 step178
  have step267 (X0 : G) :  sK0 ≠ X0 := superpose step202 step10
  subsumption step267 step202


@[equational_result]
theorem Finite.Equation677_and_Equation2291_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (s ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (s ◇ (s ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose step11 step11
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step11 step16
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step24 step14
  have step39 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step32
  have step40 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step39 step11
  have step45 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step39 step14
  have step76 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step16 step40
  have step95 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step45 step76
  have step98 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step40 step95
  have step100 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := superpose step39 step17
  have step119 (X0 X1 : G) :  X0 = X1 := superpose step98 step100
  have step161 (X0 : G) :  sK0 ≠ X0 := superpose step119 step12
  subsumption step161 step119


@[equational_result]
theorem Finite.Equation677_and_Equation229_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step13 step13
  have step31 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step15 step14
  have step55 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) := superpose step16 step14
  have step60 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step19 step55
  have step69 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step60
  have step75 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step31 step69
  have step78 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step31 step75
  have step104 (X0 X1 : G) :  X0 = X1 := superpose step78 step11
  have step130 (X0 : G) :  sK0 ≠ X0 := superpose step104 step12
  subsumption step130 step104


@[equational_result]
theorem Finite.Equation677_and_Equation2293_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step26 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step20
  have step44 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) := superpose step9 step26
  have step54 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) = X0 := superpose step26 step9
  have step58 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step54
  have step62 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step9 step44
  have step65 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step58 step62
  have step67 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step9 step65
  have step69 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step9 step67
  have step599 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step69 step21
  have step648 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step599
  have step709 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := superpose step21 step648
  have step721 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step648 step12
  have step749 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step648 step721
  have step757 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose step648 step709
  have step778 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step648 step757
  have step784 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose step648 step778
  have step787 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step648 step784
  have step788 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step648 step787
  have step886 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step749 step69
  have step905 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step788 step886
  have step941 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step749 step905
  have step1321 (X0 X1 : G) :  X0 = X1 := superpose step941 step11
  have step1551 (X0 : G) :  sK0 ≠ X0 := superpose step1321 step10
  subsumption step1551 step1321


@[equational_result]
theorem Finite.Equation677_and_Equation2300_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step18
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step12
  have step44 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step25 step21
  have step120 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X0)) := superpose step24 step19
  have step140 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step12 step120
  have step164 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step140 step13
  have step187 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step44 step164
  have step290 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose step187 step140
  have step296 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step187 step290
  have step674 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step296 step19
  have step679 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step12 step674
  have step876 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step296 step679
  have step906 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step679 step19
  have step934 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step679 step906
  have step960 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step876 step934
  have step969 (X0 X1 : G) :  X0 = X1 := superpose step876 step960
  have step1119 (X0 : G) :  sK0 ≠ X0 := superpose step969 step10
  subsumption step1119 step969


@[equational_result]
theorem Finite.Equation677_and_Equation2303_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step17
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step20 step12
  have step38 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step23 step9
  have step45 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step38
  have step61 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step45 step9
  have step105 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X1)) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step61 step22
  have step112 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step45 step105
  have step126 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step45 step112
  have step130 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step61 step126
  have step131 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step61 step130
  have step205 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step131 step11
  have step206 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step45 step205
  have step220 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step131 step206
  have step243 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose step14 step11
  have step244 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose step220 step243
  have step258 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step22 step244
  have step269 (X0 X1 : G) :  X0 = X1 := superpose step220 step258
  have step325 (X0 : G) :  sK0 ≠ X0 := superpose step269 step10
  subsumption step325 step269


@[equational_result]
theorem Finite.Equation677_and_Equation231_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step11
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step12
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step19 step29
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step30 step34
  have step45 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := superpose step37 step9
  have step49 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step30 step45
  have step66 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step49 step12
  have step68 (X0 X1 : G) :  X0 = X1 := superpose step49 step66
  have step108 (X0 : G) :  sK0 ≠ X0 := superpose step68 step10
  subsumption step108 step68


@[equational_result]
theorem Finite.Equation677_and_Equation2328_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ Y) ◇ ((Y ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : (Y ◇ (Y ◇ ((X ◇ Y) ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (Y ◇ (s ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step31 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step18
  have step44 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X1) := superpose step12 step31
  have step55 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step31 step16
  have step57 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step16 step55
  have step73 (X0 X1 X2 : G) :  ((X2 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step14 step31
  have step84 (X0 X1 X2 : G) :  ((X2 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose step44 step73
  have step95 (X0 X1 : G) :  X0 = X1 := superpose step57 step84
  have step130 (X0 : G) :  sK0 ≠ X0 := superpose step95 step13
  subsumption step130 step95


@[equational_result]
theorem Finite.Equation677_and_Equation2330_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step11 step9
  have step20 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step20
  have step32 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step17 step12
  have step37 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step32
  have step104 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step28
  have step131 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step17 step104
  have step140 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step37 step131
  have step147 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose step9 step140
  have step150 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step9 step147
  have step168 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step150 step12
  have step471 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step168 step21
  have step488 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X1 := superpose step150 step471
  have step507 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step150 step488
  have step684 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step507 step12
  have step688 (X0 X1 : G) :  X0 = X1 := superpose step507 step684
  have step842 (X0 : G) :  sK0 ≠ X0 := superpose step688 step10
  subsumption step842 step688


@[equational_result]
theorem Finite.Equation677_and_Equation2338_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X Y : G) : (Y ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (Y ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : (Y ◇ (Y ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step15 step14
  have step30 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := superpose step16 step16
  have step47 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step17 step14
  have step50 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step25 step47
  have step98 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step18 step15
  have step99 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0))) := superpose step18 step16
  have step104 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step25 step99
  have step105 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step50 step98
  have step119 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose step25 step104
  have step120 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step25 step105
  have step126 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step30 step119
  have step127 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step25 step120
  have step132 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step126 step127
  have step136 (X0 X1 : G) :  X0 = X1 := superpose step126 step132
  have step167 (X0 : G) :  sK0 ≠ X0 := superpose step136 step13
  subsumption step167 step136


@[equational_result]
theorem Finite.Equation677_and_Equation2340_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step23 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step25 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0)) := superpose step9 step11
  have step27 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step11 step9
  have step28 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step27
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step35 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step35 step12
  have step77 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step43 step35
  have step78 (X0 X1 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose step43 step9
  have step237 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ X0)) := superpose step28 step32
  have step261 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ X0) := superpose step12 step237
  have step303 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) = X1 := superpose step261 step77
  have step312 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step9 step303
  have step359 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0))) := superpose step28 step23
  have step383 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step261 step23
  have step411 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step312 step383
  have step427 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) := superpose step312 step359
  have step444 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step312 step411
  have step456 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose step312 step427
  have step473 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X0)) := superpose step312 step444
  have step483 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step312 step456
  have step495 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step12 step473
  have step503 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step312 step483
  have step514 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step312 step503
  have step529 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose step312 step78
  have step544 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step495 step529
  have step560 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose step261 step25
  have step598 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X0) = ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) := superpose step514 step560
  have step615 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X0) = X2 := superpose step544 step598
  have step627 (X0 X2 : G) :  X0 = X2 := superpose step544 step615
  have step708 (X0 : G) :  sK0 ≠ X0 := superpose step627 step10
  subsumption step708 step627


@[equational_result]
theorem Finite.Equation677_and_Equation2443_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step17 step20
  have step28 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step17 step26
  have step43 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose step11 step28
  have step53 (X0 X1 : G) :  X0 = X1 := superpose step17 step43
  have step75 (X0 : G) :  sK0 ≠ X0 := superpose step53 step10
  subsumption step75 step53


@[equational_result]
theorem Finite.Equation677_and_Equation2446_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose step9 step11
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step11
  have step22 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose step11 step9
  have step43 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step22
  have step96 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose step20 step22
  have step100 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose step20 step11
  have step102 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose step43 step100
  have step103 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step20 step102
  have step104 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step96 step103
  have step110 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step104
  have step235 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step110 step12
  have step242 (X0 X1 : G) :  X0 = X1 := superpose step104 step235
  have step334 (X0 : G) :  sK0 ≠ X0 := superpose step242 step10
  subsumption step334 step242


@[equational_result]
theorem Finite.Equation677_and_Equation2456_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step11
  have step19 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step11
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step19 step9
  have step22 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step19 step11
  have step26 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step35 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step22 step26
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step35
  have step134 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step18 step9
  have step137 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose step18 step11
  have step139 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose step38 step137
  have step145 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose step18 step139
  have step146 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step134 step145
  have step165 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step146 step12
  have step169 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step146 step165
  have step196 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step27 step12
  have step199 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step27 step146
  have step215 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step146 step199
  have step218 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step146 step196
  have step239 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step169 step215
  have step241 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step169 step218
  have step256 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step239 step241
  have step265 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step239 step256
  have step272 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step239 step265
  have step310 (X0 X1 : G) :  X0 = X1 := superpose step272 step11
  have step417 (X0 : G) :  sK0 ≠ X0 := superpose step310 step10
  subsumption step417 step310


@[equational_result]
theorem Finite.Equation677_and_Equation2459_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step12 step9
  have step26 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step9 step19
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step22
  have step49 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) := superpose step26 step12
  have step50 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = X0 := superpose step26 step22
  have step57 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) := superpose step27 step49
  have step65 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step50 step57
  have step227 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step65 step65
  have step245 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step65 step12
  have step252 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ X0) := superpose step245 step227
  have step261 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step27 step252
  have step270 (X0 X1 : G) :  X0 = X1 := superpose step245 step261
  have step333 (X0 : G) :  sK0 ≠ X0 := superpose step270 step10
  subsumption step333 step270


@[equational_result]
theorem Finite.Equation677_and_Equation2466_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := superpose step9 step17
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step23
  have step48 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose step15 step11
  have step53 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose step27 step48
  have step62 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose step15 step53
  have step67 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step27 step62
  have step71 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step27 step15
  have step83 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step67 step71
  have step119 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step67 step12
  have step122 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step83 step119
  have step127 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step67 step122
  have step129 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step27 step127
  have step177 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step129 step12
  have step182 (X0 X1 : G) :  X0 = X1 := superpose step129 step177
  have step273 (X0 : G) :  sK0 ≠ X0 := superpose step182 step10
  subsumption step273 step182


@[equational_result]
theorem Finite.Equation677_and_Equation2469_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step9 step18
  have step32 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step23
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step23
  have step39 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step32
  have step40 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step9 step39
  have step41 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) := superpose step33 step40
  have step42 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step33 step41
  have step43 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step33 step42
  have step44 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step33 step43
  have step54 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step33 step17
  have step73 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step44 step54
  have step78 (X0 X1 : G) :  X0 = X1 := superpose step44 step73
  have step108 (X0 : G) :  sK0 ≠ X0 := superpose step78 step10
  subsumption step108 step78


@[equational_result]
theorem Finite.Equation677_and_Equation2493_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step11
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step13 step18
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step19 step13
  have step22 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step9
  have step26 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step9 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step35 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose step19 step26
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose step22 step35
  have step40 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step13
  have step42 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step21 step11
  have step53 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose step37 step12
  have step56 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step40 step53
  have step58 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step42 step56
  have step91 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step58 step12
  have step94 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step58 step91
  have step114 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step28 step28
  have step138 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step94 step114
  have step160 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose step94 step138
  have step179 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step94 step160
  have step187 (X0 X1 : G) :  X0 = X1 := superpose step94 step179
  have step226 (X0 : G) :  sK0 ≠ X0 := superpose step187 step10
  subsumption step226 step187


@[equational_result]
theorem Finite.Equation677_and_Equation2496_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose step9 step17
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step22
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step29 step22
  have step39 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose step29 step9
  have step80 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step39 step39
  have step102 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step29 step80
  have step162 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose step37 step12
  have step174 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose step29 step162
  have step186 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step102 step174
  have step196 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step39 step186
  have step232 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step196 step196
  have step246 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step196 step11
  have step253 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step29 step246
  have step267 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step196 step253
  have step301 (X0 X1 : G) :  ((((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) = X1 := superpose step18 step16
  have step305 (X0 X1 : G) :  (((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose step267 step301
  have step330 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step232 step305
  have step345 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose step267 step330
  have step354 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step232 step345
  have step360 (X0 X1 : G) :  X0 = X1 := superpose step267 step354
  have step415 (X0 : G) :  sK0 ≠ X0 := superpose step360 step10
  subsumption step415 step360


@[equational_result]
theorem Finite.Equation677_and_Equation2503_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step12 step9
  have step46 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step24 step12
  have step47 (X0 X1 : G) :  X0 = X1 := superpose step24 step46
  have step86 (X0 : G) :  sK0 ≠ X0 := superpose step47 step10
  subsumption step86 step47


@[equational_result]
theorem Finite.Equation677_and_Equation2504_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X Y : G) : (Y ◇ (((X ◇ Y) ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ ((s ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) := superpose step11 step11
  have step19 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ X1) := superpose step15 step17
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step14 step15
  have step39 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose step11 step16
  have step55 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = X1 := superpose step19 step39
  have step60 (X0 X1 : G) :  X0 = X1 := superpose step27 step55
  have step80 (X0 : G) :  sK0 ≠ X0 := superpose step60 step12
  subsumption step80 step60


@[equational_result]
theorem Finite.Equation677_and_Equation2533_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step9 step19
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step24
  have step131 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0)) := superpose step24 step20
  have step150 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step131
  have step155 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X0) := superpose step30 step150
  have step159 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step30 step155
  have step175 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step159 step159
  have step183 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step159 step20
  have step185 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step159 step12
  have step188 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step185 step183
  have step202 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose step175 step188
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step175 step202
  have step338 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0))) := superpose step12 step175
  have step396 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose step175 step338
  have step417 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step212 step396
  have step430 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step159 step417
  have step463 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step15 step175
  have step464 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step430 step463
  have step490 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step430 step464
  have step575 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step490 step12
  have step592 (X0 X1 : G) :  X0 = X1 := superpose step490 step575
  have step740 (X0 : G) :  sK0 ≠ X0 := superpose step592 step10
  subsumption step740 step592


@[equational_result]
theorem Finite.Equation677_and_Equation2541_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ Y) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((Y ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step13
  have step55 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose step41 step14
  have step57 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step41 step11
  have step85 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) := superpose step16 step55
  have step107 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step57 step85
  have step110 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step41 step107
  have step112 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step41 step110
  have step165 (X0 X1 : G) :  X0 = X1 := superpose step112 step11
  have step235 (X0 : G) :  sK0 ≠ X0 := superpose step165 step12
  subsumption step235 step165


@[equational_result]
theorem Finite.Equation677_and_Equation2543_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step11 step9
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step9 step24
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step12 step9
  have step35 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step33
  have step47 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose step35 step25
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step25
  have step54 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose step25 step9
  have step55 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose step25 step12
  have step58 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose step35 step55
  have step59 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step54
  have step64 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step51 step47
  have step67 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose step51 step58
  have step68 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step35 step59
  have step73 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step51 step64
  have step76 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step51 step67
  have step77 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose step51 step68
  have step82 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step35 step76
  have step83 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step35 step77
  have step87 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step73 step82
  have step88 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step73 step83
  have step91 (X0 X1 : G) :  X0 = X1 := superpose step87 step88
  have step114 (X0 : G) :  sK0 ≠ X0 := superpose step91 step10
  subsumption step114 step91


@[equational_result]
theorem Finite.Equation677_and_Equation2646_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step17 step16
  have step42 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step18
  have step64 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step42 step12
  have step67 (X0 X1 : G) :  X0 = X1 := superpose step18 step64
  have step107 (X0 : G) :  sK0 ≠ X0 := superpose step67 step10
  subsumption step107 step67


@[equational_result]
theorem Finite.Equation677_and_Equation2649_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step9
  have step29 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose step24 step20
  have step36 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step24 step9
  have step55 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step36 step11
  have step74 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step29 step12
  have step79 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step36 step74
  have step90 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step55 step79
  have step92 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step24 step90
  have step101 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step92 step12
  have step112 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose step24 step101
  have step124 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step36 step112
  have step138 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step22 step22
  have step166 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step124 step138
  have step184 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose step124 step166
  have step200 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step124 step184
  have step209 (X0 X1 : G) :  X0 = X1 := superpose step124 step200
  have step247 (X0 : G) :  sK0 ≠ X0 := superpose step209 step10
  subsumption step247 step209


@[equational_result]
theorem Finite.Equation677_and_Equation2652_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) = X0 := superpose step9 step11
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step16
  have step23 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step12
  have step38 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0)) := superpose step23 step12
  have step40 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step38
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step49 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step46
  have step51 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step40 step49
  have step55 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ X0)) := superpose step51 step23
  have step56 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step51 step18
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step51 step12
  have step60 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step51 step57
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step40 step60
  have step66 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step51 step17
  have step68 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step51 step17
  have step90 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step68
  have step92 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step23 step66
  have step98 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step51 step90
  have step100 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step51 step92
  have step103 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step40 step98
  have step106 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step100 step103
  have step109 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step51 step106
  have step115 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step63 step51
  have step144 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose step14 step11
  have step145 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step55 step144
  have step153 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step109 step145
  have step156 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step56 step153
  have step159 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose step115 step156
  have step161 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose step115 step159
  have step163 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step115 step161
  have step237 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step15 step17
  have step242 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose step12 step237
  have step276 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step163 step242
  have step399 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step276 step12
  have step406 (X0 X1 : G) :  X0 = X1 := superpose step276 step399
  have step534 (X0 : G) :  sK0 ≠ X0 := superpose step406 step10
  subsumption step534 step406


@[equational_result]
theorem Finite.Equation677_and_Equation2659_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) = X0 := superpose step16 step17
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step16 step12
  have step43 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step26 step11
  have step54 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step19 step16
  have step61 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step54
  have step74 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step61 step16
  have step87 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step16 step18
  have step89 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step22 step18
  have step111 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step89
  have step112 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step61 step87
  have step121 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose step74 step111
  have step122 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose step43 step112
  have step126 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step61 step121
  have step127 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step74 step122
  have step143 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step126 step18
  have step159 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step127 step143
  have step164 (X0 X1 : G) :  X0 = X1 := superpose step126 step159
  have step230 (X0 : G) :  sK0 ≠ X0 := superpose step164 step10
  subsumption step230 step164


@[equational_result]
theorem Finite.Equation677_and_Equation2662_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step11 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step20
  have step25 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step23
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step25 step9
  have step34 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step25 step16
  have step45 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose step16 step12
  have step46 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step29 step45
  have step53 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step29 step46
  have step59 (X0 X1 : G) :  X0 = X1 := superpose step34 step53
  have step80 (X0 : G) :  sK0 ≠ X0 := superpose step59 step10
  subsumption step80 step59


@[equational_result]
theorem Finite.Equation677_and_Equation2696_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step11
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step18 step11
  have step23 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step24 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step12
  have step33 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step24
  have step34 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step23
  have step36 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step28 step33
  have step134 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step34 step25
  have step156 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step134
  have step163 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step28 step156
  have step168 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step36 step163
  have step174 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step25 step168
  have step189 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step168 step12
  have step192 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step168 step189
  have step200 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step168 step174
  have step203 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step192 step200
  have step326 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step203 step12
  have step329 (X0 X1 : G) :  X0 = X1 := superpose step203 step326
  have step456 (X0 : G) :  sK0 ≠ X0 := superpose step329 step10
  subsumption step456 step329


@[equational_result]
theorem Finite.Equation677_and_Equation2706_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step11
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step11
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step18 step16
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step18 step9
  have step23 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step22
  have step24 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step12
  have step35 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step23 step24
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step23 step9
  have step49 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) := superpose step11 step35
  have step54 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step35 step12
  have step59 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step42 step54
  have step63 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step12 step49
  have step70 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step42 step59
  have step72 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step23 step70
  have step78 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step11 step72
  have step86 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step72 step12
  have step91 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step72 step86
  have step96 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose step63 step78
  have step101 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step91 step96
  have step102 (X0 X1 : G) :  X0 = X1 := superpose step91 step101
  have step149 (X0 : G) :  sK0 ≠ X0 := superpose step102 step10
  subsumption step149 step102


@[equational_result]
theorem Finite.Equation677_and_Equation2709_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0) = X0 := superpose step9 step9
  have step17 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step17
  have step28 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step12
  have step52 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0)) := superpose step28 step12
  have step56 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step52
  have step91 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = ((X0 ◇ X0) ◇ X0) := superpose step9 step56
  have step111 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose step56 step22
  have step158 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))))))) = X0 := superpose step13 step22
  have step159 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))))) := superpose step13 step28
  have step162 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step91 step159
  have step163 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose step91 step158
  have step179 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step111 step162
  have step180 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step111 step163
  have step209 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose step180 step28
  have step212 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose step180 step56
  have step225 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose step180 step212
  have step228 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step179 step209
  have step238 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step180 step225
  have step374 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step238 step12
  have step387 (X0 X1 : G) :  X0 = X1 := superpose step228 step374
  have step528 (X0 : G) :  sK0 ≠ X0 := superpose step387 step10
  subsumption step528 step387


@[equational_result]
theorem Finite.Equation677_and_Equation2733_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step11
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step11
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step16
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step19 step9
  have step23 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step22
  have step24 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step34 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step23 step24
  have step36 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step23 step34
  have step40 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose step23 step9
  have step46 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step23 step40
  have step52 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) := superpose step11 step36
  have step57 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step36 step12
  have step60 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step46 step57
  have step64 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step12 step52
  have step69 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step46 step60
  have step71 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step23 step69
  have step77 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step11 step71
  have step85 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step71 step12
  have step89 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step71 step85
  have step94 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose step64 step77
  have step98 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step89 step94
  have step99 (X0 X1 : G) :  X0 = X1 := superpose step89 step98
  have step154 (X0 : G) :  sK0 ≠ X0 := superpose step99 step10
  subsumption step154 step99


@[equational_result]
theorem Finite.Equation677_and_Equation2734_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : ((((Y ◇ Y) ◇ X) ◇ Y) ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ Y) ◇ ((X ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Y) ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step14 step16
  have step26 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step14 step16
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step31 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step11 step13
  have step36 (X0 X1 X2 : G) :  ((X0 ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose step13 step11
  have step38 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step14
  have step52 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step31 step38
  have step213 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step36 step16
  have step217 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step11 step213
  have step233 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step217 step16
  have step234 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step217 step16
  have step245 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step234 step233
  have step250 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step27 step245
  have step254 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose step14 step26
  have step255 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose step38 step26
  have step262 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step26 step14
  have step265 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step250 step262
  have step270 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose step250 step255
  have step271 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose step250 step254
  have step273 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step52 step265
  have step276 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step250 step271
  have step277 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step273
  have step284 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step277 step15
  have step288 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step277 step13
  have step289 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step250 step288
  have step293 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step270 step284
  have step296 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step276 step289
  have step302 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step293 step296
  have step307 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step52 step302
  have step309 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step14 step307
  have step318 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step27 step15
  have step319 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step277 step318
  have step328 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step319
  have step333 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step293 step328
  have step337 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step309 step333
  have step374 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step337 step13
  have step384 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step337 step374
  have step435 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step337 step24
  have step446 (X0 X1 X2 : G) :  (((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) = X2 := superpose step24 step36
  have step453 (X0 X1 X2 : G) :  (((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) = X2 := superpose step337 step446
  have step461 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step337 step435
  have step482 (X0 X1 X2 : G) :  (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose step337 step453
  have step489 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ X0) := superpose step384 step461
  have step508 (X0 X1 X2 : G) :  (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X1) = X2 := superpose step384 step482
  have step513 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step337 step489
  have step528 (X0 X1 X2 : G) :  (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X2 := superpose step337 step508
  have step541 (X0 X1 X2 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X2 := superpose step513 step528
  have step543 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose step513 step541
  have step545 (X0 X2 : G) :  X0 = X2 := superpose step384 step543
  have step615 (X0 : G) :  sK0 ≠ X0 := superpose step545 step12
  subsumption step615 step545


@[equational_result]
theorem Finite.Equation677_and_Equation2736_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose step9 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose step9 step18
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step11
  have step37 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step9
  have step53 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step25
  have step78 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step37 step53
  have step87 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose step37 step78
  have step91 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose step9 step87
  have step94 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step9 step91
  have step95 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step37 step94
  have step146 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step95 step11
  have step149 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step37 step146
  have step160 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step95 step149
  have step201 (X0 X1 : G) :  X0 = X1 := superpose step160 step95
  have step303 (X0 : G) :  sK0 ≠ X0 := superpose step201 step10
  subsumption step303 step201


@[equational_result]
theorem Finite.Equation677_and_Equation2744_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : (Y ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ Y) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step14 step14
  have step29 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step11
  have step31 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step15 step13
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step81 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step11 step31
  have step106 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step14 step81
  have step107 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step106 step16
  have step109 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step106 step16
  have step119 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step109 step107
  have step122 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step36 step119
  have step143 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step122 step29
  have step150 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step122 step16
  have step156 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step150
  have step160 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step31 step143
  have step169 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose step156 step160
  have step177 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step156 step169
  have step279 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose step156 step14
  have step283 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step156 step31
  have step313 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step177 step283
  have step351 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) := superpose step29 step34
  have step372 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X1 := superpose step34 step14
  have step381 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose step177 step372
  have step395 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)))) := superpose step177 step351
  have step413 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := superpose step177 step381
  have step423 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) := superpose step313 step395
  have step439 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step279 step413
  have step448 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step156 step423
  have step464 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = X1 := superpose step177 step439
  have step472 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step156 step448
  have step487 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step20 step464
  have step494 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step156 step472
  have step507 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step156 step487
  have step513 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step177 step494
  have step527 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose step507 step513
  have step541 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step507 step527
  have step552 (X0 X1 : G) :  X0 = X1 := superpose step507 step541
  have step619 (X0 : G) :  sK0 ≠ X0 := superpose step552 step12
  subsumption step619 step552


@[equational_result]
theorem Finite.Equation677_and_Equation2746_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step20
  have step29 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step17 step29
  have step37 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step31 step9
  have step51 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step12
  have step56 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose step37 step51
  have step61 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose step31 step56
  have step76 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step37 step11
  have step93 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step61 step76
  have step115 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step93 step37
  have step181 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step115 step12
  have step184 (X0 X1 : G) :  X0 = X1 := superpose step115 step181
  have step273 (X0 : G) :  sK0 ≠ X0 := superpose step184 step10
  subsumption step273 step184


@[equational_result]
theorem Finite.Equation677_and_Equation2849_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))) = X0 := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose step16 step14
  have step20 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose step16 step18
  have step22 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose step16 step20
  have step24 (X0 X1 : G) :  X0 = X1 := superpose step16 step22
  have step43 (X0 : G) :  sK0 ≠ X0 := superpose step24 step10
  subsumption step43 step24


@[equational_result]
theorem Finite.Equation677_and_Equation2852_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose step9 step19
  have step36 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step11 step18
  have step110 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step36 step12
  have step113 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step36 step110
  have step133 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = X1 := superpose step20 step25
  have step143 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step20 step36
  have step154 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step36 step143
  have step159 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := superpose step36 step133
  have step175 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step113 step154
  have step180 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step113 step159
  have step193 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step175 step180
  have step233 (X0 X1 : G) :  X0 = X1 := superpose step193 step11
  have step333 (X0 : G) :  sK0 ≠ X0 := superpose step233 step10
  subsumption step333 step233


@[equational_result]
theorem Finite.Equation677_and_Equation2862_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step9 step20
  have step33 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step27 step12
  have step34 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step27 step12
  have step37 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step34 step33
  have step39 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step23 step37
  have step49 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose step39 step12
  have step55 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step23 step12
  have step59 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step49 step55
  have step86 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step39 step22
  have step109 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step59 step86
  have step117 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step59 step109
  have step122 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step39 step117
  have step127 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step59 step122
  have step130 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step59 step127
  have step133 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step59 step130
  have step222 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step133 step22
  have step226 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step222
  have step242 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step59 step226
  have step252 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step59 step242
  have step282 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step22 step17
  have step327 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step252 step282
  have step361 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step252 step327
  have step394 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step361
  have step420 (X0 X1 : G) :  X0 = X1 := superpose step252 step394
  have step493 (X0 : G) :  sK0 ≠ X0 := superpose step420 step10
  subsumption step493 step420


@[equational_result]
theorem Finite.Equation677_and_Equation2872_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X0 := superpose step9 step16
  have step23 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step12
  have step37 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) ◇ X0)) := superpose step23 step12
  have step39 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step37
  have step67 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step39 step9
  have step68 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step39 step12
  have step123 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step67 step12
  have step126 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step17 step123
  have step129 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step68 step126
  have step194 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step129 step20
  have step195 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step129 step9
  have step204 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step129 step194
  have step291 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose step204 step39
  have step313 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step195 step291
  have step507 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step313
  have step723 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step507 step12
  have step742 (X0 X1 : G) :  X0 = X1 := superpose step313 step723
  have step907 (X0 : G) :  sK0 ≠ X0 := superpose step742 step10
  subsumption step907 step742


@[equational_result]
theorem Finite.Equation677_and_Equation2899_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step9 step19
  have step28 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step25 step12
  have step29 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step25 step12
  have step31 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step28
  have step32 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step22 step31
  have step44 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step22 step9
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step44
  have step54 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step48 step32
  have step65 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step48 step54
  have step75 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step32 step21
  have step103 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step48 step75
  have step112 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step48 step103
  have step118 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step65 step112
  have step121 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step65 step118
  have step124 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step48 step121
  have step220 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step124 step12
  have step223 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step124 step220
  have step377 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step223 step12
  have step385 (X0 X1 : G) :  X0 = X1 := superpose step223 step377
  have step502 (X0 : G) :  sK0 ≠ X0 := superpose step385 step10
  subsumption step502 step385


@[equational_result]
theorem Finite.Equation677_and_Equation2902_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose step9 step16
  have step23 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step12
  have step38 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X0)) := superpose step23 step12
  have step40 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step38
  have step69 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step40
  have step74 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step40 step40
  have step78 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step40 step12
  have step105 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step74 step69
  have step107 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step78 step105
  have step113 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step18 step17
  have step145 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step40 step113
  have step153 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step78 step145
  have step158 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step107 step153
  have step160 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step107 step158
  have step163 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step160 step20
  have step172 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step160 step163
  have step217 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step172 step40
  have step239 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step172 step217
  have step266 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step17 step15
  have step309 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step239 step266
  have step346 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step11 step309
  have step381 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step172 step346
  have step462 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = X0 := superpose step381 step40
  have step491 (X0 X1 : G) :  X0 = X1 := superpose step239 step462
  have step622 (X0 : G) :  sK0 ≠ X0 := superpose step491 step10
  subsumption step622 step491


@[equational_result]
theorem Finite.Equation677_and_Equation2909_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose step9 step17
  have step47 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step19 step9
  have step62 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X0)) := superpose step22 step18
  have step80 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step62
  have step87 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step47 step18
  have step89 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step47 step11
  have step101 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step80 step87
  have step142 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step89 step22
  have step143 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step89 step9
  have step241 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step143 step18
  have step243 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step47 step241
  have step253 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step101 step243
  have step257 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step142 step253
  have step519 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step13 step12
  have step536 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X1 ◇ X1)) := superpose step18 step519
  have step562 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X1) := superpose step257 step536
  have step578 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose step22 step562
  have step588 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose step257 step578
  have step602 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step588 step588
  have step638 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step588 step20
  have step643 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step257 step638
  have step663 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step257 step602
  have step668 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step588 step643
  have step682 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step663 step668
  have step688 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose step588 step682
  have step690 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step257 step688
  have step922 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step15 step690
  have step924 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step690 step690
  have step975 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step924 step922
  have step1099 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step975 step690
  have step1184 (X0 X1 : G) :  X0 = X1 := superpose step975 step1099
  have step1390 (X0 : G) :  sK0 ≠ X0 := superpose step1184 step10
  subsumption step1390 step1184


@[equational_result]
theorem Finite.Equation677_and_Equation2939_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X0 := superpose step9 step13
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := superpose step9 step19
  have step32 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))))) = X0 := superpose step14 step11
  have step35 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose step24 step32
  have step53 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ X0)) := superpose step24 step12
  have step64 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step35 step53
  have step146 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step64 step64
  have step155 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step64 step12
  have step201 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step64 step155
  have step237 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step64 step20
  have step276 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step146 step237
  have step299 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step201 step276
  have step315 (X0 X1 : G) :  X0 = X1 := superpose step201 step299
  have step363 (X0 : G) :  sK0 ≠ X0 := superpose step315 step10
  subsumption step363 step315


@[equational_result]
theorem Finite.Equation677_and_Equation2946_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X0 := superpose step9 step18
  have step29 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step23 step12
  have step47 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) ◇ X0)) := superpose step29 step12
  have step53 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step47
  have step87 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step53 step9
  have step88 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step53 step12
  have step151 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step87 step12
  have step154 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step19 step151
  have step156 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step88 step154
  have step234 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose step156 step53
  have step237 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step156 step9
  have step254 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step237 step234
  have step345 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step254 step12
  have step355 (X0 X1 : G) :  X0 = X1 := superpose step254 step345
  have step479 (X0 : G) :  sK0 ≠ X0 := superpose step355 step10
  subsumption step479 step355


@[equational_result]
theorem Finite.Equation677_and_Equation2947_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step30 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step14 step12
  have step31 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step14 step10
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step30 step14
  have step40 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step35
  have step41 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step40 step12
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step40 step10
  have step76 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step41 step14
  have step81 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ X0) := superpose step42 step76
  have step89 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step31 step14
  have step94 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step81 step89
  have step98 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step42 step94
  have step146 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step42 step14
  have step150 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step81 step146
  have step191 (X0 X1 : G) :  X0 = X1 := superpose step150 step98
  have step347 (X0 : G) :  sK0 ≠ X0 := superpose step191 step11
  subsumption step347 step191


@[equational_result]
theorem Finite.Equation677_and_Equation2949_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step24 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := superpose step11 step9
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := superpose step9 step24
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step40 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step25
  have step70 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step40 step11
  have step89 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step70 step21
  have step95 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)))) := superpose step25 step29
  have step97 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step29
  have step125 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := superpose step40 step97
  have step127 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := superpose step9 step95
  have step131 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step89 step125
  have step132 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step89 step127
  have step135 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose step131 step132
  have step143 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step135 step135
  have step144 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step135 step70
  have step171 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X0 := superpose step144 step143
  have step178 (X0 X1 : G) :  X0 = X1 := superpose step144 step171
  have step262 (X0 : G) :  sK0 ≠ X0 := superpose step178 step10
  subsumption step262 step178


@[equational_result]
theorem Finite.Equation677_and_Equation3052_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)))) = X0 := superpose step9 step11
  have step15 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) = X0 := superpose step15 step13
  have step19 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := superpose step15 step17
  have step21 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step15 step19
  have step23 (X0 X1 : G) :  X0 = X1 := superpose step15 step21
  have step42 (X0 : G) :  sK0 ≠ X0 := superpose step23 step10
  subsumption step42 step23


@[equational_result]
theorem Finite.Equation677_and_Equation3055_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step15 step17
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step15
  have step31 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step15 step12
  have step33 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step15 step31
  have step89 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step22 step22
  have step94 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step22 step15
  have step106 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step33 step94
  have step109 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step25 step89
  have step116 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X1 := superpose step106 step109
  have step121 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose step106 step116
  have step123 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step106 step121
  have step124 (X0 X1 : G) :  X0 = X1 := superpose step106 step123
  have step155 (X0 : G) :  sK0 ≠ X0 := superpose step124 step10
  subsumption step155 step124


@[equational_result]
theorem Finite.Equation677_and_Equation3065_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step9
  have step30 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step16 step12
  have step33 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step16 step30
  have step127 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose step33 step18
  have step148 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step127
  have step156 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose step29 step148
  have step161 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step29 step156
  have step165 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step18 step161
  have step186 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step161 step12
  have step193 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step161 step186
  have step203 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step161 step165
  have step207 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step193 step203
  have step282 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step207 step12
  have step291 (X0 X1 : G) :  X0 = X1 := superpose step207 step282
  have step411 (X0 : G) :  sK0 ≠ X0 := superpose step291 step10
  subsumption step411 step291


@[equational_result]
theorem Finite.Equation677_and_Equation3102_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step9
  have step24 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step28 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step36 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step28
  have step50 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step36 step9
  have step51 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step36 step50
  have step58 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step36 step51
  have step62 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step36 step58
  have step77 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step62 step11
  have step80 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose step15 step77
  have step89 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step62 step80
  have step102 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = ((((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step9 step29
  have step128 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step89 step102
  have step133 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step89 step128
  have step137 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step15 step133
  have step140 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step15 step137
  have step155 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step140 step12
  have step161 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step140 step155
  have step233 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step29 step161
  have step252 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step161 step12
  have step263 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step161 step252
  have step272 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step161 step233
  have step277 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step263 step272
  have step291 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step29 step24
  have step331 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step277 step291
  have step359 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step277 step331
  have step382 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step359
  have step402 (X0 X1 : G) :  X0 = X1 := superpose step277 step382
  have step462 (X0 : G) :  sK0 ≠ X0 := superpose step402 step10
  subsumption step462 step402


@[equational_result]
theorem Finite.Equation677_and_Equation3112_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) = X0 := superpose step9 step17
  have step55 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) ◇ X0)) := superpose step22 step18
  have step73 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step55
  have step84 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1) := superpose step73 step73
  have step95 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step73 step18
  have step100 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step73 step9
  have step110 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step9 step100
  have step113 (X0 X1 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step18 step95
  have step115 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose step9 step84
  have step120 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step110 step113
  have step125 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step110 step120
  have step128 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step115 step125
  have step131 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X0) := superpose step110 step128
  have step132 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step110 step131
  have step234 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step15 step12
  have step243 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose step132 step234
  have step274 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X0 := superpose step132 step243
  have step316 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step274
  have step322 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step274 step18
  have step345 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step132 step322
  have step357 (X0 X1 : G) :  X0 = X1 := superpose step316 step345
  have step454 (X0 : G) :  sK0 ≠ X0 := superpose step357 step10
  subsumption step454 step357


@[equational_result]
theorem Finite.Equation677_and_Equation3139_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = X0 := superpose step9 step17
  have step62 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) ◇ X0)) := superpose step22 step18
  have step73 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step62
  have step79 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) := superpose step73 step73
  have step86 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step73 step18
  have step87 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step73 step18
  have step91 (X0 X1 : G) :  (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step73 step9
  have step101 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step9 step91
  have step103 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step18 step87
  have step108 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose step9 step79
  have step111 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step86 step103
  have step114 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step101 step108
  have step116 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step101 step111
  have step119 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) := superpose step101 step116
  have step120 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step114 step119
  have step121 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step114 step120
  have step122 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step101 step121
  have step288 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step18 step114
  have step327 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step114 step288
  have step339 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step122 step327
  have step343 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step101 step339
  have step417 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step343 step12
  have step430 (X0 X1 : G) :  X0 = X1 := superpose step343 step417
  have step562 (X0 : G) :  sK0 ≠ X0 := superpose step430 step10
  subsumption step562 step430


@[equational_result]
theorem Finite.Equation677_and_Equation3142_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step11
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step11
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step18 step16
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step18 step9
  have step23 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step20 step22
  have step24 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step23
  have step25 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step9 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step36 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step24 step25
  have step41 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose step24 step9
  have step57 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step36 step12
  have step62 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step41 step57
  have step71 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X0) := superpose step13 step62
  have step77 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step24 step71
  have step115 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step27 step12
  have step127 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step77 step115
  have step139 (X0 X1 : G) :  X0 = X1 := superpose step77 step127
  have step177 (X0 : G) :  sK0 ≠ X0 := superpose step139 step10
  subsumption step177 step139


@[equational_result]
theorem Finite.Equation677_and_Equation3149_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)))) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose step9 step18
  have step30 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step23 step12
  have step49 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0))) ◇ X0)) := superpose step30 step12
  have step51 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step49
  have step89 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step51 step9
  have step92 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step51 step12
  have step100 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step51 step9
  have step107 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step100 step92
  have step110 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step51 step89
  have step112 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose step100 step107
  have step115 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step110 step112
  have step117 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step110 step115
  have step129 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step30 step14
  have step137 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose step117 step129
  have step148 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = X0 := superpose step117 step137
  have step155 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step117 step148
  have step159 (X0 X1 : G) :  X0 = X1 := superpose step117 step155
  have step209 (X0 : G) :  sK0 ≠ X0 := superpose step159 step10
  subsumption step209 step159


@[equational_result]
theorem Finite.Equation677_and_Equation3150_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step12 step13
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step22
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step26 step10
  have step33 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0))) = X1 := superpose step10 step14
  have step49 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step29 step33
  have step58 (X0 X2 : G) :  X0 = X2 := superpose step49 step49
  have step136 (X0 : G) :  sK0 ≠ X0 := superpose step58 step11
  subsumption step136 step58


@[equational_result]
theorem Finite.Equation677_and_Equation3152_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step11 step9
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step21
  have step40 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step12
  have step111 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) ◇ X0)) := superpose step40 step12
  have step113 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step111
  have step180 (X0 X2 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X2) = X2 := superpose step113 step9
  have step187 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose step113 step18
  have step207 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose step9 step187
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step180 step207
  have step435 (X0 X1 : G) :  X0 = X1 := superpose step214 step11
  have step540 (X0 : G) :  sK0 ≠ X0 := superpose step435 step10
  subsumption step540 step435


@[equational_result]
theorem Finite.Equation677_and_Equation323_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step11 step9
  have step30 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step9 step12
  have step36 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step9 step30
  have step38 (X0 X1 : G) :  X0 = X1 := superpose step18 step36
  have step51 (X0 : G) :  sK0 ≠ X0 := superpose step38 step10
  subsumption step51 step38


@[equational_result]
theorem Finite.Equation677_and_Equation3254_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X1 ◇ X1) := superpose step11 step9
  have step27 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ X1) := superpose step11 step20
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step11
  have step33 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step30 step27
  have step37 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step51 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step33 step37
  have step57 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step33 step51
  have step58 (X0 X1 : G) :  X0 = X1 := superpose step33 step57
  have step75 (X0 : G) :  sK0 ≠ X0 := superpose step58 step10
  subsumption step75 step58


@[equational_result]
theorem Finite.Equation677_and_Equation3255_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step29 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step17 step23
  have step30 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step12 step21
  have step32 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose step17 step29
  have step34 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step30 step32
  have step35 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step17 step34
  have step53 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step35 step12
  have step54 (X0 X1 : G) :  X0 = X1 := superpose step35 step53
  have step81 (X0 : G) :  sK0 ≠ X0 := superpose step54 step10
  subsumption step81 step54


@[equational_result]
theorem Finite.Equation677_and_Equation3256_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X0 := superpose step12 step16
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step12
  have step32 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step25
  have step59 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step32 step21
  have step97 (X0 X1 : G) :  X0 = X1 := superpose step59 step11
  have step168 (X0 : G) :  sK0 ≠ X0 := superpose step97 step10
  subsumption step168 step97


@[equational_result]
theorem Finite.Equation677_and_Equation3258_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step12 step16
  have step22 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step21 step21
  have step50 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step22 step12
  have step51 (X0 X1 : G) :  X0 = X1 := superpose step21 step50
  have step86 (X0 : G) :  sK0 ≠ X0 := superpose step51 step10
  subsumption step86 step51


@[equational_result]
theorem Finite.Equation677_and_Equation3259_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step12 step17
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step23 step23
  have step32 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ X1) := superpose step23 step9
  have step69 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step27 step12
  have step72 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step32 step69
  have step102 (X0 X2 : G) :  X0 = X2 := superpose step72 step72
  have step189 (X0 : G) :  sK0 ≠ X0 := superpose step102 step10
  subsumption step189 step102


@[equational_result]
theorem Finite.Equation677_and_Equation3262_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X0 := superpose step12 step19
  have step28 (X0 X2 : G) :  X0 = X2 := superpose step24 step24
  have step107 (X0 : G) :  sK0 ≠ X0 := superpose step28 step10
  subsumption step107 step28


@[equational_result]
theorem Finite.Equation677_and_Equation3268_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step9 step11
  have step21 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step9 step12
  have step28 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step9
  have step50 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step21
  have step64 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose step28 step50
  have step70 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ X1) := superpose step28 step64
  have step74 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step28 step70
  have step81 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step28 step9
  have step90 (X0 X1 : G) :  X0 = X1 := superpose step74 step81
  have step137 (X0 : G) :  sK0 ≠ X0 := superpose step90 step10
  subsumption step137 step90


@[equational_result]
theorem Finite.Equation677_and_Equation3269_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step18 step22
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step25 step11
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step26
  have step95 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose step33 step13
  have step122 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step33 step95
  have step237 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose step9 step18
  have step239 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step13 step18
  have step243 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step18 step18
  have step250 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose step18 step11
  have step259 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose step33 step250
  have step266 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X0) := superpose step33 step243
  have step270 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose step33 step239
  have step272 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step33 step237
  have step275 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step11 step259
  have step282 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose step11 step266
  have step285 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) := superpose step9 step270
  have step286 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step33 step272
  have step291 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose step33 step282
  have step294 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose step33 step285
  have step296 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step291 step294
  have step297 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step33 step296
  have step412 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step297 step11
  have step420 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step297 step286
  have step422 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step286 step420
  have step765 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step412 step422
  have step770 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) := superpose step12 step422
  have step780 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step422 step422
  have step791 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose step422 step12
  have step808 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step297 step791
  have step820 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := superpose step422 step770
  have step830 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step780 step808
  have step836 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step422 step820
  have step866 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step20 step20
  have step867 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose step422 step20
  have step885 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step20 step286
  have step891 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step20 step297
  have step900 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := superpose step20 step122
  have step915 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step422 step900
  have step922 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step422 step891
  have step928 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step291 step885
  have step944 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step422 step867
  have step945 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step297 step866
  have step974 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step422 step915
  have step981 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step422 step922
  have step984 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step297 step928
  have step996 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step780 step944
  have step997 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step297 step945
  have step1025 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step422 step974
  have step1033 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step836 step984
  have step1039 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step297 step996
  have step1040 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step981 step997
  have step1063 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step275 step1025
  have step1070 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step297 step1033
  have step1073 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose step981 step1039
  have step1074 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step981 step1040
  have step1094 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step1063 step1070
  have step1097 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step422 step1074
  have step1111 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = X1 := superpose step1073 step1094
  have step1114 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step830 step1097
  have step1126 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step765 step1111
  have step1137 (X0 X1 : G) :  X0 = X1 := superpose step1114 step1126
  have step1207 (X0 : G) :  sK0 ≠ X0 := superpose step1137 step10
  subsumption step1207 step1137


@[equational_result]
theorem Finite.Equation677_and_Equation3271_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step17 step12
  have step38 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step28 step11
  have step39 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step28 step9
  have step40 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step39 step38
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step40
  have step69 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step41 step17
  have step193 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step18 step9
  have step208 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step69 step193
  have step224 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose step41 step208
  have step419 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step69 step12
  have step431 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step12 step419
  have step488 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X1))) := superpose step18 step13
  have step509 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) := superpose step13 step41
  have step510 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step41 step509
  have step530 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X1)) := superpose step41 step488
  have step545 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step431 step510
  have step564 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step431 step530
  have step575 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step9 step545
  have step593 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step41 step564
  have step604 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X1 := superpose step41 step575
  have step622 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step69 step593
  have step648 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step224 step622
  have step670 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step604 step648
  have step712 (X0 X1 : G) :  X0 = X1 := superpose step670 step11
  have step871 (X0 : G) :  sK0 ≠ X0 := superpose step712 step10
  subsumption step871 step712


@[equational_result]
theorem Finite.Equation677_and_Equation3272_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := superpose step9 step9
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step9 step12
  have step23 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step49 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step13 step9
  have step101 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step12
  have step103 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step15 step11
  have step104 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step103
  have step106 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step101 step104
  have step138 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step106 step9
  have step160 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step23 step12
  have step163 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step21 step160
  have step166 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step138 step163
  have step168 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step166
  have step169 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step106 step168
  have step180 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step169 step11
  have step181 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step49 step180
  have step214 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step21 step13
  have step215 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step21 step12
  have step218 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step181 step215
  have step219 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step181 step214
  have step238 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step218
  have step239 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step169 step219
  have step253 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step181 step238
  have step254 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step106 step239
  have step262 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose step181 step254
  have step268 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step181 step262
  have step273 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step181 step268
  have step379 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step253
  have step403 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step253 step9
  have step409 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step181 step403
  have step425 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X0 := superpose step273 step409
  have step434 (X0 X1 : G) :  X0 = X1 := superpose step379 step425
  have step548 (X0 : G) :  sK0 ≠ X0 := superpose step434 step10
  subsumption step548 step434


@[equational_result]
theorem Finite.Equation677_and_Equation3279_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step9
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step9 step12
  have step31 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose step20 step9
  have step32 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step20 step12
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step9
  have step35 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step24 step32
  have step147 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step34 step12
  have step151 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step24 step147
  have step154 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step35 step151
  have step164 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step34 step25
  have step189 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step154 step164
  have step190 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step154 step189
  have step191 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step20 step190
  have step192 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step154 step191
  have step194 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step20 step192
  have step198 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step192 step31
  have step213 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step198 step194
  have step504 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose step25 step15
  have step537 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step213 step504
  have step560 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step213 step537
  have step579 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step213 step560
  have step592 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X1) := superpose step9 step579
  have step594 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step213 step592
  have step662 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step594 step12
  have step679 (X0 X1 : G) :  X0 = X1 := superpose step594 step662
  have step859 (X0 : G) :  sK0 ≠ X0 := superpose step679 step10
  subsumption step859 step679


@[equational_result]
theorem Finite.Equation677_and_Equation3309_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step9 step12
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step12 step16
  have step22 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step21 step21
  have step32 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose step21 step18
  have step51 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose step22 step32
  have step60 (X0 X1 : G) :  X0 = X1 := superpose step21 step51
  have step87 (X0 : G) :  sK0 ≠ X0 := superpose step60 step10
  subsumption step87 step60


@[equational_result]
theorem Finite.Equation677_and_Equation3315_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step12 step17
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step12
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step26
  have step42 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step33 step22
  have step64 (X0 X1 : G) :  X0 = X1 := superpose step42 step11
  have step120 (X0 : G) :  sK0 ≠ X0 := superpose step64 step10
  subsumption step120 step64


@[equational_result]
theorem Finite.Equation677_and_Equation3316_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X1 := superpose step12 step17
  have step30 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step23 step12
  have step33 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step23 step30
  have step109 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step33 step12
  have step111 (X0 X1 : G) :  X0 = X1 := superpose step33 step109
  have step166 (X0 : G) :  sK0 ≠ X0 := superpose step111 step10
  subsumption step166 step111


@[equational_result]
theorem Finite.Equation677_and_Equation3318_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step25 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step12 step18
  have step27 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step25
  have step58 (X0 X1 : G) :  X0 = X1 := superpose step27 step11
  have step98 (X0 : G) :  sK0 ≠ X0 := superpose step58 step10
  subsumption step98 step58


@[equational_result]
theorem Finite.Equation677_and_Equation333_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose step11 step9
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step16
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step24 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose step12 step9
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step22
  have step28 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step19
  have step30 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step18 step26
  have step31 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step30
  have step73 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose step17 step11
  have step79 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose step9 step73
  have step87 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step24
  have step110 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose step79 step87
  have step115 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step9 step110
  have step128 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step28 step12
  have step140 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step13 step128
  have step153 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step115 step140
  have step156 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step31 step153
  have step177 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step156 step12
  have step180 (X0 X1 : G) :  X0 = X1 := superpose step156 step177
  have step248 (X0 : G) :  sK0 ≠ X0 := superpose step180 step10
  subsumption step248 step180


@[equational_result]
theorem Finite.Equation677_and_Equation3346_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step39 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step17 step12
  have step50 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step39 step12
  have step53 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step39 step12
  have step54 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step39 step11
  have step55 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step54
  have step61 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step20 step11
  have step62 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose step53 step61
  have step66 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step55 step62
  have step68 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step66
  have step70 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step50 step68
  have step71 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step70 step9
  have step195 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step17 step18
  have step223 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step70 step195
  have step233 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step55 step223
  have step238 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step70 step233
  have step242 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step17 step238
  have step243 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step70 step242
  have step244 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) := superpose step70 step243
  have step245 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step71 step244
  have step324 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step18 step15
  have step337 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step245 step324
  have step370 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X1 ◇ X0))) := superpose step71 step337
  have step393 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step370
  have step411 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose step70 step393
  have step436 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step11 step411
  have step462 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step411 step12
  have step481 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step411 step462
  have step498 (X0 X1 : G) :  X0 = X1 := superpose step436 step481
  have step605 (X0 : G) :  sK0 ≠ X0 := superpose step498 step10
  subsumption step605 step498


@[equational_result]
theorem Finite.Equation677_and_Equation3457_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step11
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ X1) := superpose step11 step9
  have step18 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step17 step16
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ X1) := superpose step17 step15
  have step20 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step17 step14
  have step21 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step18 step19
  have step22 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step18 step20
  have step23 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step17 step21
  have step24 (X0 X1 : G) :  X0 = X1 := superpose step22 step23
  have step41 (X0 : G) :  sK0 ≠ X0 := superpose step24 step10
  subsumption step41 step24


@[equational_result]
theorem Finite.Equation677_and_Equation3458_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step11 step9
  have step18 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step17 step16
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) := superpose step17 step22
  have step26 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step12 step19
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) := superpose step18 step24
  have step29 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step26 step27
  have step31 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step18 step29
  have step43 (X0 X1 : G) :  X0 = X1 := superpose step31 step11
  have step67 (X0 : G) :  sK0 ≠ X0 := superpose step43 step10
  subsumption step67 step43


@[equational_result]
theorem Finite.Equation677_and_Equation3461_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step12 step18
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step24
  have step36 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step24 step12
  have step41 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step24 step36
  have step166 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step41 step12
  have step168 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step41 step24
  have step175 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step41 step168
  have step177 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose step35 step166
  have step186 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step175 step177
  have step193 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step35 step186
  have step196 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step24 step19
  have step249 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step41 step196
  have step270 (X0 X1 : G) :  X0 = X1 := superpose step193 step249
  have step320 (X0 : G) :  sK0 ≠ X0 := superpose step270 step10
  subsumption step320 step270


@[equational_result]
theorem Finite.Equation677_and_Equation3462_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step12 step21
  have step69 (X0 X1 : G) :  X0 = X1 := superpose step30 step16
  have step89 (X0 : G) :  sK0 ≠ X0 := superpose step69 step10
  subsumption step89 step69


@[equational_result]
theorem Finite.Equation677_and_Equation3464_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step12 step18
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step12
  have step34 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step29
  have step62 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step34 step26
  have step108 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step62 step12
  have step111 (X0 X1 : G) :  X0 = X1 := superpose step62 step108
  have step175 (X0 : G) :  sK0 ≠ X0 := superpose step111 step10
  subsumption step175 step111


@[equational_result]
theorem Finite.Equation677_and_Equation3465_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = X0 := superpose step12 step21
  have step37 (X0 X2 : G) :  X0 = X2 := superpose step28 step28
  have step75 (X0 : G) :  sK0 ≠ X0 := superpose step37 step10
  subsumption step75 step37


@[equational_result]
theorem Finite.Equation677_and_Equation3472_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step12 step9
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step16 step22
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step21
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step24 step25
  have step29 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step11
  have step31 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step26 step29
  have step32 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step31
  have step45 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step32 step9
  have step72 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step45 step11
  have step75 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step32 step72
  have step79 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step45 step75
  have step90 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step13 step11
  have step96 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step79 step90
  have step97 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step79 step96
  have step98 (X0 X1 : G) :  X0 = X1 := superpose step79 step97
  have step124 (X0 : G) :  sK0 ≠ X0 := superpose step98 step10
  subsumption step124 step98


@[equational_result]
theorem Finite.Equation677_and_Equation3474_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step26 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step12 step9
  have step33 (X0 X2 : G) :  X0 = X2 := superpose step26 step26
  have step88 (X0 : G) :  sK0 ≠ X0 := superpose step33 step10
  subsumption step88 step33


@[equational_result]
theorem Finite.Equation677_and_Equation3482_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) = X1 := superpose step9 step11
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step14 step16
  have step22 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1)) = X1 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step9 step12
  have step30 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose step21 step22
  have step42 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step19 step21
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step12
  have step51 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step30 step45
  have step52 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step19 step42
  have step55 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step51 step52
  have step58 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step55 step9
  have step114 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step9 step30
  have step153 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := superpose step15 step114
  have step171 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step55 step153
  have step179 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step55 step171
  have step448 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step23 step58
  have step449 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step55 step448
  have step476 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step179 step449
  have step536 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0))) := superpose step12 step179
  have step585 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose step179 step536
  have step600 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step476 step585
  have step609 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step58 step600
  have step649 (X0 X1 X2 : G) :  (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = (X2 ◇ ((X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) := superpose step14 step13
  have step657 (X0 X1 X2 : G) :  (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X2 := superpose step609 step649
  have step691 (X1 X2 : G) :  X1 = X2 := superpose step609 step657
  have step764 (X0 : G) :  sK0 ≠ X0 := superpose step691 step10
  subsumption step764 step691


@[equational_result]
theorem Finite.Equation677_and_Equation3509_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step12 step21
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step17 step12
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step28
  have step62 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step33 step27
  have step103 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step62 step12
  have step104 (X0 X1 : G) :  X0 = X1 := superpose step62 step103
  have step151 (X0 : G) :  sK0 ≠ X0 := superpose step104 step10
  subsumption step151 step104


@[equational_result]
theorem Finite.Equation677_and_Equation3511_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step25 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step12 step18
  have step32 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step17 step12
  have step35 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ X0) := superpose step25 step32
  have step43 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step25 step12
  have step47 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step35 step43
  have step50 (X0 X2 : G) :  X0 = X2 := superpose step47 step47
  have step108 (X0 : G) :  sK0 ≠ X0 := superpose step50 step10
  subsumption step108 step50


@[equational_result]
theorem Finite.Equation677_and_Equation3512_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X1 := superpose step12 step18
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step16 step9
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step28
  have step36 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step24 step12
  have step41 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step24 step36
  have step133 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step41 step12
  have step135 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step41 step24
  have step142 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step41 step135
  have step144 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose step29 step133
  have step152 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step142 step144
  have step157 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step29 step152
  have step165 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) = X0 := superpose step12 step13
  have step184 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := superpose step157 step165
  have step197 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step157 step184
  have step208 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step157 step197
  have step218 (X0 X1 : G) :  X0 = X1 := superpose step157 step208
  have step258 (X0 : G) :  sK0 ≠ X0 := superpose step218 step10
  subsumption step258 step218


@[equational_result]
theorem Finite.Equation677_and_Equation3519_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step12 step9
  have step33 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step12 step22
  have step74 (X0 X1 : G) :  X0 = X1 := superpose step33 step26
  have step118 (X0 : G) :  sK0 ≠ X0 := superpose step74 step10
  subsumption step118 step74


@[equational_result]
theorem Finite.Equation677_and_Equation3521_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X1 := superpose step12 step18
  have step44 (X0 X1 : G) :  X0 = X1 := superpose step24 step11
  have step68 (X0 : G) :  sK0 ≠ X0 := superpose step44 step10
  subsumption step68 step44


@[equational_result]
theorem Finite.Equation677_and_Equation3546_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step11
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step12 step9
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step22
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step16 step24
  have step31 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step9
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step31
  have step49 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step38 step9
  have step121 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step18 step12
  have step124 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step38 step121
  have step136 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step49 step124
  have step146 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose step27 step136
  have step152 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step49 step146
  have step160 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step12 step152
  have step172 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step152 step12
  have step175 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step49 step172
  have step181 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step152 step175
  have step184 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step38 step181
  have step205 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step12 step14
  have step232 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step184 step205
  have step259 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step184 step232
  have step282 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step160 step259
  have step300 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step184 step282
  have step312 (X0 X1 : G) :  X0 = X1 := superpose step184 step300
  have step352 (X0 : G) :  sK0 ≠ X0 := superpose step312 step10
  subsumption step352 step312


@[equational_result]
theorem Finite.Equation677_and_Equation3660_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose step11 step9
  have step20 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step20 step19
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step21 step26
  have step36 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step21 step32
  have step40 (X0 X1 : G) :  X0 = X1 := superpose step21 step36
  have step53 (X0 : G) :  sK0 ≠ X0 := superpose step40 step10
  subsumption step53 step40


@[equational_result]
theorem Finite.Equation677_and_Equation3661_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step15
  have step20 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step13 step19
  have step26 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step9
  have step54 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step20 step26
  have step65 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step20 step12
  have step66 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step26 step65
  have step74 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step20 step66
  have step78 (X0 X1 : G) :  X0 = X1 := superpose step54 step74
  have step96 (X0 : G) :  sK0 ≠ X0 := superpose step78 step10
  subsumption step96 step78


@[equational_result]
theorem Finite.Equation677_and_Equation3664_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose step11 step9
  have step33 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step17 step12
  have step34 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step17 step33
  have step54 (X0 X2 : G) :  X0 = X2 := superpose step34 step34
  have step123 (X0 : G) :  sK0 ≠ X0 := superpose step54 step10
  subsumption step123 step54


@[equational_result]
theorem Finite.Equation677_and_Equation3674_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step20 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step20
  have step59 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step25
  have step65 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step25 step11
  have step67 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step65
  have step79 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step59 step12
  have step84 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step67 step79
  have step85 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step84
  have step106 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step85 step14
  have step109 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step85 step25
  have step227 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step21 step25
  have step228 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step21 step106
  have step244 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step106 step228
  have step245 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step106 step227
  have step271 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step109 step244
  have step272 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step109 step245
  have step293 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose step271 step272
  have step311 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step271 step293
  have step325 (X0 X1 : G) :  X0 = X1 := superpose step271 step311
  have step380 (X0 : G) :  sK0 ≠ X0 := superpose step325 step10
  subsumption step380 step325


@[equational_result]
theorem Finite.Equation677_and_Equation3678_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X2 ◇ X1) ◇ (X2 ◇ X2)) := superpose step9 step9
  have step17 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step49 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step18 step11
  have step99 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step49
  have step109 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step99
  have step178 (X0 X1 X2 : G) :  (X2 ◇ X2) = (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose step13 step19
  have step187 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose step109 step178
  have step247 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step109 step49
  have step258 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step187 step247
  have step435 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose step258 step49
  have step447 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X1) ◇ (X0 ◇ X0)) := superpose step258 step17
  have step591 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X1) := superpose step435 step17
  have step801 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose step591 step435
  have step818 (X1 X2 : G) :  (X1 ◇ X1) = X2 := superpose step447 step801
  have step903 (X0 X2 : G) :  X0 = X2 := superpose step818 step818
  have step1192 (X0 : G) :  sK0 ≠ X0 := superpose step903 step10
  subsumption step1192 step903


@[equational_result]
theorem Finite.Equation677_and_Equation3685_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X2 : G) :  (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step29 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step32 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step15 step29
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step32 step11
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step35
  have step60 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step16 step9
  have step63 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step16 step11
  have step65 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step41 step63
  have step68 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose step41 step60
  have step81 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step41 step65
  have step83 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step41 step68
  have step92 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step41 step81
  have step98 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step83 step92
  have step105 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step41 step9
  have step110 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step98 step105
  have step115 (X0 X1 : G) :  X0 = X1 := superpose step98 step110
  have step176 (X0 : G) :  sK0 ≠ X0 := superpose step115 step10
  subsumption step176 step115


@[equational_result]
theorem Finite.Equation677_and_Equation3703_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X3 X4 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X3 ◇ X4) ◇ (X4 ◇ X3)) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step9 step9
  have step38 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step19 step11
  have step39 (X0 X1 X2 : G) :  (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2))) = X2 := superpose step9 step11
  have step59 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X2)) = X2 := superpose step9 step12
  have step159 (X0 X1 X2 X3 : G) :  (X3 ◇ X2) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3))) := superpose step13 step12
  have step160 (X2 X3 : G) :  (X2 ◇ X3) = (X3 ◇ X2) := superpose step59 step159
  have step196 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step160 step11
  have step656 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := superpose step38 step196
  have step690 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step160 step656
  have step711 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step38 step690
  have step803 (X0 X1 X2 : G) :  (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) = (X0 ◇ ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) ◇ X0)) := superpose step39 step196
  have step817 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step39 step196
  have step819 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)))) := superpose step160 step817
  have step833 (X0 X1 X2 : G) :  (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0))) := superpose step160 step803
  have step859 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0))) := superpose step711 step819
  have step872 (X0 X1 X2 : G) :  (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) = X0 := superpose step39 step833
  have step891 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) = X0 := superpose step39 step859
  have step906 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step872 step891
  have step927 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step906 step19
  have step1140 (X0 X1 : G) :  X0 = X1 := superpose step927 step906
  have step1436 (X0 : G) :  sK0 ≠ X0 := superpose step1140 step10
  subsumption step1436 step1140


@[equational_result]
theorem Finite.Equation677_and_Equation3712_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step11 step9
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step24
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step27
  have step30 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose step29 step9
  have step38 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step29 step19
  have step50 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose step19 step12
  have step51 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step30 step50
  have step60 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step38 step51
  have step66 (X0 X1 : G) :  X0 = X1 := superpose step38 step60
  have step87 (X0 : G) :  sK0 ≠ X0 := superpose step66 step10
  subsumption step87 step66


@[equational_result]
theorem Finite.Equation677_and_Equation3714_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step9
  have step28 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step24 step12
  have step44 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step28 step9
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step44
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step14 step45
  have step51 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step49
  have step61 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step65 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step12 step61
  have step79 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step65 step24
  have step85 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step65 step12
  have step86 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step65 step11
  have step93 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose step65 step86
  have step94 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step51 step85
  have step100 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step79 step93
  have step101 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step65 step94
  have step102 (X0 X1 : G) :  X0 = X1 := superpose step100 step101
  have step145 (X0 : G) :  sK0 ≠ X0 := superpose step102 step10
  subsumption step145 step102


@[equational_result]
theorem Finite.Equation677_and_Equation3721_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step17 step15
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ X0) := superpose step17 step18
  have step60 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step19 step11
  have step69 (X0 X1 X2 : G) :  (X2 ◇ (X0 ◇ X1)) = X2 := superpose step19 step17
  have step75 (X0 X1 : G) :  X0 = X1 := superpose step69 step60
  have step94 (X0 : G) :  sK0 ≠ X0 := superpose step75 step10
  subsumption step94 step75


@[equational_result]
theorem Finite.Equation677_and_Equation3725_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step26 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step18 step12
  have step29 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step26
  have step46 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step9
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step46
  have step65 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step49 step11
  have step102 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step65 step11
  have step211 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step20
  have step226 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step20 step65
  have step243 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step102 step226
  have step255 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step102 step211
  have step274 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step65 step255
  have step287 (X0 X1 : G) :  X0 = X1 := superpose step243 step274
  have step343 (X0 : G) :  sK0 ≠ X0 := superpose step287 step10
  subsumption step343 step287


@[equational_result]
theorem Finite.Equation677_and_Equation3752_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose step11 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step14 step11
  have step34 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose step14 step12
  have step41 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step14 step34
  have step46 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step33
  have step50 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := superpose step33 step14
  have step73 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step11
  have step82 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step41 step73
  have step101 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step82 step12
  have step108 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step101
  have step121 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) = (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)))) := superpose step33 step13
  have step132 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) := superpose step11 step13
  have step153 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) := superpose step108 step132
  have step163 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose step108 step121
  have step175 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose step17 step153
  have step185 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step50 step163
  have step194 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose step108 step175
  have step203 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose step108 step185
  have step213 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step108 step203
  have step230 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose step108 step13
  have step232 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose step108 step230
  have step400 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose step13 step18
  have step418 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0)) := superpose step11 step18
  have step434 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))) := superpose step18 step15
  have step439 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))) := superpose step194 step434
  have step451 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0)) := superpose step194 step418
  have step467 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose step194 step400
  have step474 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))))) := superpose step194 step439
  have step483 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step17 step451
  have step498 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose step108 step467
  have step505 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose step46 step474
  have step513 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step194 step483
  have step526 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step232 step498
  have step533 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step108 step505
  have step540 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step232 step513
  have step552 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step108 step526
  have step559 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step232 step533
  have step564 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step108 step540
  have step575 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step108 step552
  have step581 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step213 step559
  have step592 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose step564 step575
  have step594 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step564 step581
  have step600 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step564 step592
  have step602 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step232 step594
  have step607 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step600 step602
  have step610 (X0 X1 : G) :  X0 = X1 := superpose step600 step607
  have step658 (X0 : G) :  sK0 ≠ X0 := superpose step610 step10
  subsumption step658 step610


@[equational_result]
theorem Finite.Equation677_and_Equation3759_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) := superpose step9 step12
  have step24 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step9
  have step27 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose step9 step19
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step24 step9
  have step37 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step11
  have step40 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose step33 step37
  have step42 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step24 step40
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step33 step11
  have step48 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step42 step46
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step48
  have step77 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step50 step9
  have step143 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step27 step12
  have step148 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose step77 step143
  have step162 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose step50 step148
  have step168 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step33 step162
  have step190 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step168 step12
  have step195 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step77 step190
  have step198 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step168 step195
  have step199 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step50 step198
  have step265 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step199 step12
  have step271 (X0 X1 : G) :  X0 = X1 := superpose step199 step265
  have step352 (X0 : G) :  sK0 ≠ X0 := superpose step271 step10
  subsumption step352 step271


@[equational_result]
theorem Finite.Equation677_and_Equation377_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  X0 = X1 := superpose step17 step16
  have step38 (X0 : G) :  sK0 ≠ X0 := superpose step18 step10
  subsumption step38 step18


@[equational_result]
theorem Finite.Equation677_and_Equation378_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step12 step9
  have step23 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step20
  have step26 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step23
  have step38 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step26 step12
  have step42 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step38
  have step89 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step9 step22
  have step117 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step9 step89
  have step122 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X1 := superpose step42 step117
  have step145 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step122 step12
  have step149 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step122 step145
  have step238 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step149 step11
  have step254 (X0 X1 : G) :  X0 = X1 := superpose step122 step238
  have step320 (X0 : G) :  sK0 ≠ X0 := superpose step254 step10
  subsumption step320 step254


@[equational_result]
theorem Finite.Equation677_and_Equation3864_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose step11 step9
  have step22 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step9 step12
  have step32 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X1) := superpose step11 step17
  have step44 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step22 step22
  have step50 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step32 step44
  have step61 (X0 X1 : G) :  X0 = X1 := superpose step50 step22
  have step119 (X0 : G) :  sK0 ≠ X0 := superpose step61 step10
  subsumption step119 step61


@[equational_result]
theorem Finite.Equation677_and_Equation3867_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step21 step12
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step16 step24
  have step39 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step21 step27
  have step42 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step27 step12
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step27 step42
  have step47 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step39 step46
  have step130 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step19
  have step172 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step16 step130
  have step178 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step27 step172
  have step182 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step47 step178
  have step185 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step9 step182
  have step187 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step47 step185
  have step208 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step187 step19
  have step209 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step208
  have step222 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step47 step209
  have step230 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step47 step222
  have step256 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step19 step15
  have step305 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step230 step256
  have step340 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step230 step305
  have step372 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step340
  have step399 (X0 X1 : G) :  X0 = X1 := superpose step230 step372
  have step466 (X0 : G) :  sK0 ≠ X0 := superpose step399 step10
  subsumption step466 step399


@[equational_result]
theorem Finite.Equation677_and_Equation3870_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step9 step17
  have step24 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step20 step9
  have step28 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step20 step16
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step16
  have step37 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step30
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step37
  have step97 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step22 step12
  have step100 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step28 step97
  have step114 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step39 step100
  have step122 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose step24 step114
  have step126 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ X1) := superpose step39 step122
  have step128 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step39 step126
  have step149 (X0 X1 : G) :  X0 = X1 := superpose step128 step11
  have step235 (X0 : G) :  sK0 ≠ X0 := superpose step149 step10
  subsumption step235 step149


@[equational_result]
theorem Finite.Equation677_and_Equation3877_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step20 step9
  have step41 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step22 step12
  have step45 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step19 step9
  have step55 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step45 step12
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step22 step55
  have step81 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step18
  have step83 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step22 step18
  have step94 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1) := superpose step18 step9
  have step105 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step41 step94
  have step111 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose step12 step83
  have step113 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step22 step81
  have step119 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step57 step113
  have step122 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step111 step119
  have step123 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step105 step122
  have step131 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step123 step22
  have step232 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step18 step131
  have step262 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step41 step232
  have step266 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step123 step262
  have step285 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step17 step18
  have step301 (X0 X1 : G) :  X0 = X1 := superpose step266 step285
  have step370 (X0 : G) :  sK0 ≠ X0 := superpose step301 step10
  subsumption step370 step301


@[equational_result]
theorem Finite.Equation677_and_Equation3878_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose step9 step17
  have step34 (X0 X1 : G) :  X0 = X1 := superpose step22 step20
  have step77 (X0 : G) :  sK0 ≠ X0 := superpose step34 step10
  subsumption step77 step34


@[equational_result]
theorem Finite.Equation677_and_Equation3880_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step20
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step21 step24
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step25 step11
  have step27 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step25 step12
  have step29 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step27
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step29
  have step135 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9 step14
  have step163 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose step26 step135
  have step172 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step30 step163
  have step175 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step172
  have step177 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step30 step175
  have step179 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step177
  have step181 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step26 step179
  have step201 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step181 step11
  have step206 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step30 step201
  have step217 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step181 step206
  have step342 (X0 X1 : G) :  X0 = X1 := superpose step217 step11
  have step491 (X0 : G) :  sK0 ≠ X0 := superpose step342 step10
  subsumption step491 step342


@[equational_result]
theorem Finite.Equation677_and_Equation3888_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step23 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step15 step23
  have step48 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step29 step29
  have step60 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step29 step9
  have step61 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose step26 step60
  have step62 (X0 X1 : G) :  X0 = X1 := superpose step48 step61
  have step82 (X0 : G) :  sK0 ≠ X0 := superpose step62 step10
  subsumption step82 step62


@[equational_result]
theorem Finite.Equation677_and_Equation3890_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X1)) = X1 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step14 step19
  have step28 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step23 step9
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose step23 step9
  have step54 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step28 step23
  have step62 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step23 step25
  have step86 (X0 X1 X2 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X2 ◇ X2)) = X2 := superpose step9 step29
  have step102 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step29 step12
  have step617 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step17 step12
  have step619 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step102 step617
  have step720 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0))) := superpose step619 step21
  have step725 (X0 X1 X2 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) := superpose step14 step21
  have step767 (X0 X1 X2 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) := superpose step86 step725
  have step771 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step720
  have step791 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) := superpose step21 step767
  have step795 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step9 step771
  have step807 (X0 X1 X2 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) := superpose step9 step791
  have step858 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose step795 step54
  have step869 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X1 := superpose step795 step11
  have step895 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step795 step14
  have step921 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step807 step869
  have step924 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose step895 step858
  have step936 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose step921 step924
  have step942 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ X0) = X2 := superpose step921 step936
  have step946 (X0 X1 X2 : G) :  (X1 ◇ X0) = X2 := superpose step921 step942
  have step1274 (X0 X2 : G) :  X0 = X2 := superpose step946 step62
  have step1569 (X0 : G) :  sK0 ≠ X0 := superpose step1274 step10
  subsumption step1569 step1274


@[equational_result]
theorem Finite.Equation677_and_Equation3917_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ X0) := superpose step18 step21
  have step30 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step18 step28
  have step32 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step18 step18
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step12 step18
  have step42 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step18 step33
  have step43 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step32 step42
  have step54 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step30 step11
  have step61 (X0 X1 : G) :  X0 = X1 := superpose step43 step54
  have step82 (X0 : G) :  sK0 ≠ X0 := superpose step61 step10
  subsumption step82 step61


@[equational_result]
theorem Finite.Equation677_and_Equation3918_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose step19 step18
  have step33 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step11 step24
  have step377 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step11 step33
  have step383 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose step33 step11
  have step569 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step383 step383
  have step688 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step15 step12
  have step707 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) := superpose step377 step688
  have step759 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X1) := superpose step33 step707
  have step785 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) := superpose step569 step759
  have step799 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step11 step785
  have step853 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step799 step383
  have step892 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step799 step853
  have step1423 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) = X1 := superpose step33 step892
  have step1463 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) = X1 := superpose step799 step1423
  have step1489 (X0 X1 : G) :  X0 = X1 := superpose step892 step1463
  have step1682 (X0 : G) :  sK0 ≠ X0 := superpose step1489 step10
  subsumption step1682 step1489


@[equational_result]
theorem Finite.Equation677_and_Equation3927_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose step20 step9
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose step20 step16
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step23 step9
  have step90 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose step27 step12
  have step140 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step27 step53
  have step235 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step20 step140
  have step247 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step140 step11
  have step266 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step247 step235
  have step295 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step23 step15
  have step332 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1))) := superpose step266 step295
  have step357 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step12 step332
  have step448 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X1 := superpose step27 step17
  have step456 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose step266 step17
  have step501 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step90 step456
  have step507 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) = X1 := superpose step90 step448
  have step534 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step357 step501
  have step539 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) = X1 := superpose step266 step507
  have step570 (X0 X1 : G) :  X0 = X1 := superpose step534 step539
  have step657 (X0 : G) :  sK0 ≠ X0 := superpose step570 step10
  subsumption step657 step570


@[equational_result]
theorem Finite.Equation677_and_Equation3928_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose step9 step13
  have step17 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step23 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step21 step9
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step9
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step17 step12
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step11
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step23 step31
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step24 step30
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step23 step32
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step33
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step17 step34
  have step37 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step24 step36
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step35 step37
  have step42 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step38 step9
  have step60 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = X1 := superpose step14 step12
  have step63 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := superpose step24 step60
  have step69 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step35 step63
  have step73 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step42 step69
  have step75 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step35 step73
  have step98 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step75 step12
  have step102 (X0 X1 : G) :  X0 = X1 := superpose step75 step98
  have step152 (X0 : G) :  sK0 ≠ X0 := superpose step102 step10
  subsumption step152 step102


@[equational_result]
theorem Finite.Equation677_and_Equation3952_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step20 step9
  have step26 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose step20 step16
  have step77 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose step26 step26
  have step84 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step26 step12
  have step144 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step9 step18
  have step379 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step17 step18
  have step443 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step379 step12
  have step459 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step84 step443
  have step468 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step144 step459
  have step474 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step379 step468
  have step574 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step474 step22
  have step647 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) := superpose step16 step21
  have step685 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step574 step647
  have step718 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step474 step685
  have step746 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := superpose step574 step718
  have step770 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) := superpose step22 step746
  have step787 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose step16 step770
  have step797 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step474 step787
  have step836 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step797 step9
  have step1056 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose step836 step77
  have step1109 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step574 step1056
  have step1148 (X0 X1 : G) :  X0 = X1 := superpose step836 step1109
  have step1284 (X0 : G) :  sK0 ≠ X0 := superpose step1148 step10
  subsumption step1284 step1148


@[equational_result]
theorem Finite.Equation677_and_Equation3955_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X1 := superpose step19 step18
  have step34 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step24
  have step57 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose step12 step16
  have step62 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step34 step16
  have step72 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose step34 step57
  have step144 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)))) := superpose step12 step14
  have step152 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose step62 step14
  have step167 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step16 step152
  have step175 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0))) := superpose step62 step144
  have step183 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step34 step167
  have step191 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) := superpose step62 step175
  have step202 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step183 step191
  have step209 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step72 step202
  have step213 (X0 X1 : G) :  X0 = X1 := superpose step183 step209
  have step252 (X0 : G) :  sK0 ≠ X0 := superpose step213 step10
  subsumption step252 step213


@[equational_result]
theorem Finite.Equation677_and_Equation4066_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step11 step9
  have step31 (X0 X2 : G) :  X0 = X2 := superpose step19 step19
  have step72 (X0 : G) :  sK0 ≠ X0 := superpose step31 step10
  subsumption step72 step31


@[equational_result]
theorem Finite.Equation677_and_Equation4067_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X1) := superpose step11 step9
  have step28 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X2 ◇ X1) := superpose step15 step15
  have step89 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose step28 step11
  have step94 (X0 X1 X2 : G) :  (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose step28 step11
  have step100 (X0 X2 : G) :  X0 = X2 := superpose step94 step89
  have step152 (X0 : G) :  sK0 ≠ X0 := superpose step100 step10
  subsumption step152 step100


@[equational_result]
theorem Finite.Equation677_and_Equation4070_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step16 step19
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step18
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step22
  have step31 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X0 := superpose step16 step12
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step24 step12
  have step40 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step31 step36
  have step50 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step40 step23
  have step55 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step23
  have step83 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step23 step55
  have step91 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step50 step83
  have step95 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step40 step91
  have step98 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step40 step95
  have step100 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose step16 step98
  have step102 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step40 step100
  have step110 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step23 step102
  have step117 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step102 step12
  have step121 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step102 step117
  have step125 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step40 step110
  have step129 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step121 step125
  have step132 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step102 step129
  have step134 (X0 X1 : G) :  X0 = X1 := superpose step121 step132
  have step190 (X0 : G) :  sK0 ≠ X0 := superpose step134 step10
  subsumption step190 step134


@[equational_result]
theorem Finite.Equation677_and_Equation4080_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step9
  have step17 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step14 step11
  have step23 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step9
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step23
  have step25 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step20 step24
  have step26 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step9 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step14 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step20 step12
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step14 step27
  have step38 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step35 step12
  have step40 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step35 step9
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step28 step38
  have step72 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step28
  have step76 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step35 step28
  have step96 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step14 step76
  have step100 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step41 step72
  have step105 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step25 step31
  have step108 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step31 step28
  have step114 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step31 step108
  have step116 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step41 step105
  have step117 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step14 step114
  have step118 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step35 step117
  have step179 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step25 step116
  have step184 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step116 step19
  have step185 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0)) := superpose step116 step19
  have step188 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step96 step185
  have step189 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step100 step184
  have step192 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step118 step179
  have step194 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step116 step188
  have step195 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step40 step189
  have step199 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step35 step195
  have step203 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step194 step199
  have step204 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step192 step203
  have step205 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step25 step26
  have step253 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step192 step205
  have step268 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step9 step253
  have step278 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step204 step268
  have step297 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step204 step17
  have step311 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step278 step297
  have step746 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step311 step28
  have step751 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step14 step746
  have step773 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step192 step751
  have step782 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step9 step773
  have step785 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step204 step782
  have step931 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step785 step12
  have step952 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step785 step931
  have step1063 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step28 step952
  have step1085 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step952 step12
  have step1111 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step952 step1085
  have step1116 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step952 step1063
  have step1125 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step1111 step1116
  have step1245 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step1125 step12
  have step1275 (X0 X1 : G) :  X0 = X1 := superpose step1125 step1245
  have step1488 (X0 : G) :  sK0 ≠ X0 := superpose step1275 step10
  subsumption step1488 step1275


@[equational_result]
theorem Finite.Equation677_and_Equation4083_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step21 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step9
  have step51 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step18
  have step63 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose step18 step9
  have step78 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step51
  have step191 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step20 step13
  have step219 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step191 step11
  have step238 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step219
  have step240 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step238
  have step286 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step240 step9
  have step288 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step240 step12
  have step296 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step240 step20
  have step304 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step78 step296
  have step306 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step288
  have step311 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step17 step21
  have step366 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step304 step311
  have step371 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step306 step366
  have step373 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step78 step371
  have step374 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step191 step373
  have step388 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step286 step18
  have step395 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step388
  have step401 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step306 step395
  have step404 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step374 step374
  have step425 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step374 step240
  have step428 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step401 step425
  have step448 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step401 step404
  have step469 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step306 step448
  have step473 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step428 step469
  have step476 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step240 step473
  have step779 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose step63 step18
  have step788 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose step18 step779
  have step812 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step306 step788
  have step825 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step476 step812
  have step831 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step63 step825
  have step835 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step476 step831
  have step837 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step835
  have step924 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step837 step12
  have step960 (X0 X1 : G) :  X0 = X1 := superpose step837 step924
  have step1181 (X0 : G) :  sK0 ≠ X0 := superpose step960 step10
  subsumption step1181 step960


@[equational_result]
theorem Finite.Equation677_and_Equation4090_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step20
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step23
  have step52 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step19
  have step67 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step52
  have step113 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step18
  have step132 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step27 step113
  have step151 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step132 step9
  have step203 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step151 step16
  have step315 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step203 step18
  have step334 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step9 step315
  have step342 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step203 step334
  have step526 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step342 step19
  have step531 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step12 step526
  have step541 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step531
  have step545 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step203 step541
  have step705 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step545 step11
  have step706 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step545 step705
  have step727 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step545 step706
  have step738 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step545 step727
  have step875 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ ((((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X1))) = X1 := superpose step738 step18
  have step894 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step738 step12
  have step925 (X1 X2 : G) :  ((X2 ◇ X2) ◇ X1) = X1 := superpose step894 step875
  have step949 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step738 step67
  have step963 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step67 step11
  have step964 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step925 step963
  have step978 (X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step925 step949
  have step988 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step925 step964
  have step999 (X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X1 := superpose step925 step978
  have step1007 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step925 step988
  have step1013 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step999 step1007
  have step1029 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step1013 step18
  have step1083 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step894 step1029
  have step1341 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step1083 step12
  have step1385 (X0 X1 : G) :  X0 = X1 := superpose step1083 step1341
  have step1642 (X0 : G) :  sK0 ≠ X0 := superpose step1385 step10
  subsumption step1642 step1385


@[equational_result]
theorem Finite.Equation677_and_Equation4091_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step97 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step11
  have step101 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step15 step12
  have step103 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step22 step101
  have step104 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step97 step103
  have step145 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose step9 step104
  have step154 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step104 step9
  have step274 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step22
  have step319 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step154 step274
  have step331 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step104 step319
  have step339 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step104 step331
  have step349 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step339 step12
  have step362 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step349
  have step390 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose step16 step12
  have step393 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose step154 step390
  have step406 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose step339 step393
  have step413 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step145 step406
  have step415 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step362 step413
  have step417 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step362 step415
  have step520 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step19 step22
  have step535 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose step12 step520
  have step578 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X1) := superpose step417 step535
  have step618 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ X1) := superpose step417 step578
  have step646 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step362 step618
  have step845 (X0 X1 : G) :  X0 = X1 := superpose step646 step11
  have step1033 (X0 : G) :  sK0 ≠ X0 := superpose step845 step10
  subsumption step1033 step845


@[equational_result]
theorem Finite.Equation677_and_Equation4120_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose step11 step9
  have step20 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step12 step9
  have step22 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step20 step12
  have step26 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step22
  have step31 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step26 step12
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step26 step31
  have step35 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step12 step16
  have step48 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step26 step35
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step48
  have step54 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step50 step16
  have step68 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step54
  have step104 (X0 X1 : G) :  X0 = X1 := superpose step68 step11
  have step201 (X0 : G) :  sK0 ≠ X0 := superpose step104 step10
  subsumption step201 step104


@[equational_result]
theorem Finite.Equation677_and_Equation4121_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step12
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step16 step9
  have step30 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step16 step26
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step30 step12
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step31
  have step40 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step35 step16
  have step70 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step40 step9
  have step71 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step40 step11
  have step128 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step71 step11
  have step133 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step13 step128
  have step138 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step70 step133
  have step140 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step71 step138
  have step231 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step140 step71
  have step267 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1))) = X1 := superpose step9 step18
  have step333 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) = X1 := superpose step231 step267
  have step355 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step9 step333
  have step374 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step40 step355
  have step391 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step140 step374
  have step459 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step391 step12
  have step486 (X0 X1 : G) :  X0 = X1 := superpose step391 step459
  have step632 (X0 : G) :  sK0 ≠ X0 := superpose step486 step10
  subsumption step632 step486


@[equational_result]
theorem Finite.Equation677_and_Equation412_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step9
  have step26 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step11 step9
  have step33 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step11 step26
  have step51 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step26 step12
  have step58 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step15 step51
  have step65 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ X0) := superpose step33 step58
  have step70 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step15 step65
  have step83 (X0 X1 : G) :  X0 = X1 := superpose step70 step11
  have step127 (X0 : G) :  sK0 ≠ X0 := superpose step83 step10
  subsumption step127 step83


@[equational_result]
theorem Finite.Equation677_and_Equation4128_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step12 step9
  have step157 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) := superpose step16 step18
  have step213 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step12 step157
  have step215 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step18 step213
  have step230 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step213 step9
  have step250 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step9 step230
  have step254 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step213 step215
  have step259 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step250 step254
  have step263 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step250 step259
  have step277 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step18 step15
  have step294 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step213 step15
  have step311 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step15 step213
  have step312 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step250 step311
  have step327 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose step250 step294
  have step341 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step250 step277
  have step351 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step250 step312
  have step362 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step12 step327
  have step374 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step263 step341
  have step380 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step15 step351
  have step398 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step362 step374
  have step401 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step11 step380
  have step415 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step250 step398
  have step417 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X0 := superpose step250 step401
  have step424 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step250 step415
  have step428 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step417 step424
  have step485 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step428 step21
  have step513 (X0 X1 : G) :  X0 = X1 := superpose step428 step485
  have step663 (X0 : G) :  sK0 ≠ X0 := superpose step513 step10
  subsumption step663 step513


@[equational_result]
theorem Finite.Equation677_and_Equation413_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step27 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step19
  have step29 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose step16 step27
  have step31 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step16 step29
  have step44 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step12
  have step48 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step44
  have step52 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose step16 step48
  have step54 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step16 step52
  have step66 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step54 step12
  have step70 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step54 step66
  have step135 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step70 step12
  have step136 (X0 X1 : G) :  X0 = X1 := superpose step70 step135
  have step205 (X0 : G) :  sK0 ≠ X0 := superpose step136 step10
  subsumption step205 step136


@[equational_result]
theorem Finite.Equation677_and_Equation414_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step34 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step16 step12
  have step38 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step16 step12
  have step40 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step38
  have step46 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose step40 step40
  have step126 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step46 step12
  have step136 (X1 X2 : G) :  (X1 ◇ X1) = (X2 ◇ X2) := superpose step12 step126
  have step227 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X2 ◇ X2)) := superpose step136 step40
  have step236 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step136 step12
  have step261 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step40 step17
  have step279 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step236 step261
  have step2603 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X1 := superpose step227 step236
  have step5595 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step279 step12
  have step5606 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step17 step5595
  have step5621 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step5606
  have step5771 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1)) = X0 := superpose step5621 step34
  have step5824 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) = X2 := superpose step5621 step2603
  have step5883 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose step5621 step5824
  have step5923 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose step279 step5771
  have step5945 (X0 X1 : G) :  X0 = X1 := superpose step5883 step5923
  have step6232 (X0 : G) :  sK0 ≠ X0 := superpose step5945 step10
  subsumption step6232 step5945


@[equational_result]
theorem Finite.Equation677_and_Equation416_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step15 step9
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step15 step11
  have step27 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step15 step12
  have step29 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step27
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step23 step22
  have step32 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step17
  have step41 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step32
  have step42 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step31 step41
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step29 step42
  have step44 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step31 step43
  have step50 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step31 step12
  have step53 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step31 step50
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step44 step53
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step29 step56
  have step79 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step16
  have step116 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step31 step79
  have step128 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step12 step116
  have step145 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step57 step31
  have step204 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step145 step15
  have step224 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step128 step204
  have step227 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step145 step224
  have step382 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step227 step12
  have step385 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step227 step382
  have step530 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step385 step12
  have step544 (X0 X1 : G) :  X0 = X1 := superpose step385 step530
  have step659 (X0 : G) :  sK0 ≠ X0 := superpose step544 step10
  subsumption step659 step544


@[equational_result]
theorem Finite.Equation677_and_Equation4165_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step12 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step20 step11
  have step24 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step23
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step13 step11
  have step34 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step13 step16
  have step50 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step25 step12
  have step52 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step18 step50
  have step61 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose step34 step11
  have step62 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step25 step61
  have step109 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step34 step18
  have step124 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step131 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step62 step109
  have step139 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step18 step131
  have step142 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step52 step139
  have step158 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step24 step15
  have step216 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0)) := superpose step12 step158
  have step227 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0)) := superpose step9 step216
  have step235 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step124 step227
  have step240 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step52 step235
  have step244 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step142 step240
  have step245 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step25 step244
  have step248 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step245 step16
  have step251 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step245 step11
  have step256 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step245 step12
  have step258 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step18 step256
  have step261 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step248 step258
  have step264 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step248 step261
  have step267 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step251 step264
  have step378 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose step267 step9
  have step453 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step21 step18
  have step454 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step12 step453
  have step482 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) := superpose step378 step454
  have step508 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step378 step482
  have step530 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose step378 step508
  have step638 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step530 step12
  have step640 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) := superpose step530 step12
  have step643 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step530 step15
  have step644 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1))) := superpose step530 step17
  have step651 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) := superpose step530 step9
  have step676 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step267 step651
  have step683 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1))) := superpose step378 step644
  have step684 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step378 step643
  have step687 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step378 step640
  have step718 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step378 step676
  have step725 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step267 step683
  have step726 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step638 step684
  have step728 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step530 step687
  have step747 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step378 step725
  have step748 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step718 step728
  have step759 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step530 step747
  have step766 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step748 step759
  have step769 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step748 step766
  have step770 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step267 step769
  have step871 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step770 step15
  have step872 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step770 step17
  have step873 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X0 := superpose step726 step872
  have step874 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step378 step871
  have step953 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step267 step873
  have step954 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step530 step874
  have step1011 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step953 step954
  have step1057 (X0 X1 : G) :  X0 = X1 := superpose step953 step1011
  have step1182 (X0 : G) :  sK0 ≠ X0 := superpose step1057 step10
  subsumption step1182 step1057


@[equational_result]
theorem Finite.Equation677_and_Equation417_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step69 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step12
  have step73 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step69
  have step118 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose step73 step12
  have step137 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step12
  have step144 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step118 step137
  have step148 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step144
  have step160 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose step148 step73
  have step164 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step148 step160
  have step187 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step73 step18
  have step219 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step148 step187
  have step232 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step148 step219
  have step240 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step12 step232
  have step250 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose step11 step164
  have step305 (X0 X1 : G) :  X0 = X1 := superpose step240 step250
  have step408 (X0 : G) :  sK0 ≠ X0 := superpose step305 step10
  subsumption step408 step305


@[equational_result]
theorem Finite.Equation677_and_Equation420_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step16 step12
  have step29 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step27
  have step42 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ X2) := superpose step29 step29
  have step47 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step29 step9
  have step50 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose step29 step12
  have step62 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step12
  have step64 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step50 step62
  have step87 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1))) = X1 := superpose step42 step12
  have step89 (X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step50 step87
  have step136 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step89 step17
  have step137 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step89 step12
  have step139 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step137
  have step140 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step136
  have step345 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step29 step139
  have step606 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose step42 step140
  have step1057 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step345 step12
  have step1059 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step606 step1057
  have step1134 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step64 step29
  have step1141 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := superpose step64 step47
  have step1172 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step1059 step1141
  have step1177 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X0 := superpose step1059 step1134
  have step1216 (X0 X1 : G) :  X0 = X1 := superpose step1172 step1177
  have step1336 (X0 : G) :  sK0 ≠ X0 := superpose step1216 step10
  subsumption step1336 step1216


@[equational_result]
theorem Finite.Equation677_and_Equation426_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step11
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step15 step12
  have step68 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step21 step11
  have step90 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step68 step16
  have step92 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step68 step9
  have step98 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step92 step90
  have step160 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)))) = X1 := superpose step17 step9
  have step170 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose step98 step160
  have step191 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose step98 step170
  have step209 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step98 step191
  have step221 (X0 X1 : G) :  X0 = X1 := superpose step98 step209
  have step268 (X0 : G) :  sK0 ≠ X0 := superpose step221 step10
  subsumption step268 step221


@[equational_result]
theorem Finite.Equation677_and_Equation4268_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step28 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step9 step12
  have step39 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ X1) := superpose step12 step28
  have step67 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose step39 step12
  have step72 (X0 X1 : G) :  X0 = X1 := superpose step12 step67
  have step95 (X0 : G) :  sK0 ≠ X0 := superpose step72 step10
  subsumption step95 step72


@[equational_result]
theorem Finite.Equation677_and_Equation4269_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step9 step12
  have step25 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step12 step19
  have step27 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X2 ◇ X1) := superpose step25 step25
  have step84 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose step27 step11
  have step92 (X0 X1 X2 : G) :  (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose step27 step11
  have step98 (X0 X2 : G) :  X0 = X2 := superpose step92 step84
  have step185 (X0 : G) :  sK0 ≠ X0 := superpose step98 step10
  subsumption step185 step98


@[equational_result]
theorem Finite.Equation677_and_Equation4272_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step24 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step14 step24
  have step63 (X0 X2 : G) :  X0 = X2 := superpose step26 step26
  have step100 (X0 : G) :  sK0 ≠ X0 := superpose step63 step10
  subsumption step100 step63


@[equational_result]
theorem Finite.Equation677_and_Equation427_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step13 step15
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step19 step19
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step19 step12
  have step305 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step37 step12
  have step313 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step305
  have step409 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step29 step313
  have step440 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step19 step409
  have step476 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step21 step21
  have step494 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step21 step37
  have step517 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step313 step494
  have step533 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step37 step476
  have step561 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step313 step517
  have step570 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step37 step533
  have step599 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step561 step570
  have step623 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step561 step599
  have step642 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step313 step623
  have step653 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step440 step642
  have step695 (X0 X1 : G) :  X0 = X1 := superpose step653 step11
  have step859 (X0 : G) :  sK0 ≠ X0 := superpose step695 step10
  subsumption step859 step695


@[equational_result]
theorem Finite.Equation677_and_Equation4284_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X1) := superpose step12 step18
  have step27 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose step23 step12
  have step29 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step23 step9
  have step31 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step23 step12
  have step34 (X0 X1 X2 : G) :  (X2 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose step23 step9
  have step37 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step31 step29
  have step39 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose step34 step27
  have step43 (X0 X1 : G) :  X0 = X1 := superpose step37 step39
  have step78 (X0 : G) :  sK0 ≠ X0 := superpose step43 step10
  subsumption step78 step43


@[equational_result]
theorem Finite.Equation677_and_Equation4291_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step14
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step11 step9
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step9 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step31 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose step12 step20
  have step35 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step20 step11
  have step64 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step15 step15
  have step65 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step11 step15
  have step76 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step15 step9
  have step77 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step9 step76
  have step137 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step65 step11
  have step146 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step64 step137
  have step149 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step77 step146
  have step150 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step9 step149
  have step151 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step150
  have step933 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X0 ◇ X1))) := superpose step17 step23
  have step1043 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step12 step933
  have step1409 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step1043 step35
  have step1414 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step31 step1409
  have step1502 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step26 step19
  have step1527 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step1414 step1502
  have step1573 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step151 step1527
  have step1588 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step151 step1573
  have step1596 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step151 step1588
  have step1600 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step12 step1596
  have step1656 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step1600 step12
  have step1694 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step1600 step1656
  have step1728 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step151 step1694
  have step1745 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step151 step1728
  have step2143 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step1745 step24
  have step2160 (X0 X1 : G) :  X0 = X1 := superpose step1745 step2143
  have step2425 (X0 : G) :  sK0 ≠ X0 := superpose step2160 step10
  subsumption step2425 step2160


@[equational_result]
theorem Finite.Equation677_and_Equation429_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step11 step9
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step17 step17
  have step24 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := superpose step17 step17
  have step27 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step11
  have step30 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose step17 step9
  have step31 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) := superpose step17 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) := superpose step9 step31
  have step75 (X0 X1 X2 : G) :  (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) := superpose step24 step12
  have step112 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step18
  have step144 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step75 step112
  have step588 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose step23 step18
  have step599 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X1)) := superpose step75 step588
  have step619 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) := superpose step23 step599
  have step629 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose step34 step619
  have step632 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose step144 step629
  have step765 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step632 step12
  have step782 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ X0) := superpose step12 step765
  have step904 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step782
  have step946 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X0))) := superpose step782 step16
  have step965 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose step30 step946
  have step992 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step34 step965
  have step1001 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step144 step992
  have step1243 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step1001 step9
  have step1248 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step1001 step24
  have step2217 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step1248
  have step2263 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step1248 step18
  have step2292 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step12 step2263
  have step2319 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step904 step2217
  have step2360 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step1243 step2319
  have step2383 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step1243 step2360
  have step2399 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step2292 step2383
  have step2406 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step11 step2399
  have step2410 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step2292 step2406
  have step2565 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) = X0 := superpose step2410 step27
  have step2572 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step2410 step1248
  have step2656 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = X0 := superpose step2572 step2565
  have step2701 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose step2572 step2656
  have step2728 (X0 X1 : G) :  X0 = X1 := superpose step2572 step2701
  have step2996 (X0 : G) :  sK0 ≠ X0 := superpose step2728 step10
  subsumption step2996 step2728


@[equational_result]
theorem Finite.Equation677_and_Equation4297_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X3 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := superpose step9 step9
  have step26 (X0 X1 X2 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2)) := superpose step11 step9
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step26 step32
  have step76 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step15 step12
  have step84 (X1 X2 : G) :  (X2 ◇ X2) = (X1 ◇ X1) := superpose step12 step76
  have step106 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step84 step12
  have step114 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step84 step36
  have step119 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step114 step106
  have step189 (X0 X2 : G) :  X0 = X2 := superpose step119 step119
  have step308 (X0 : G) :  sK0 ≠ X0 := superpose step189 step10
  subsumption step308 step189


@[equational_result]
theorem Finite.Equation677_and_Equation430_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step13 step12
  have step39 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step23 step9
  have step41 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose step23 step18
  have step42 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step23 step13
  have step48 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose step42 step41
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step39
  have step53 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step13 step48
  have step55 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step50 step53
  have step92 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step18 step20
  have step118 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step55 step92
  have step125 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step50 step118
  have step129 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step125
  have step132 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = X1 := superpose step50 step129
  have step138 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step132
  have step156 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step132 step9
  have step162 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose step55 step156
  have step175 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X0 := superpose step138 step162
  have step180 (X0 X1 : G) :  X0 = X1 := superpose step138 step175
  have step243 (X0 : G) :  sK0 ≠ X0 := superpose step180 step10
  subsumption step243 step180


@[equational_result]
theorem Finite.Equation677_and_Equation4305_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 X3 : G) :  (X3 ◇ ((X2 ◇ X1) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 X3 : G) :  (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X3)) := superpose step9 step9
  have step20 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step9 step9
  have step26 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := superpose step11 step9
  have step32 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step9 step12
  have step37 (X0 X1 X2 : G) :  ((X1 ◇ X0) ◇ X0) = (X2 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) := superpose step12 step9
  have step69 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step15 step11
  have step190 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose step12 step69
  have step224 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step37 step190
  have step247 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose step26 step32
  have step284 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose step224 step247
  have step290 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step224 step26
  have step299 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step224 step20
  have step304 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step224 step299
  have step318 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) := superpose step26 step33
  have step333 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose step33 step69
  have step354 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step290 step333
  have step359 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) := superpose step284 step318
  have step378 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step304 step354
  have step381 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose step224 step359
  have step394 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step378 step381
  have step542 (X0 X1 X2 X3 : G) :  ((X0 ◇ X2) ◇ X3) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3)) := superpose step13 step12
  have step593 (X0 X1 X2 X3 : G) :  ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0))) = X1 := superpose step13 step26
  have step594 (X1 X2 X3 : G) :  ((X3 ◇ (X2 ◇ X3)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X1 := superpose step290 step593
  have step641 (X0 X1 X2 X3 : G) :  ((X0 ◇ X2) ◇ X3) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose step394 step542
  have step715 (X1 X2 X3 : G) :  ((X3 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose step394 step594
  have step755 (X0 X2 X3 : G) :  ((X0 ◇ X2) ◇ X3) = X3 := superpose step290 step641
  have step818 (X1 X2 X3 : G) :  ((X3 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X1 := superpose step378 step715
  have step869 (X1 X2 : G) :  (X1 ◇ X2) = X1 := superpose step755 step818
  have step938 (X0 X1 : G) :  X0 = X1 := superpose step869 step26
  have step1203 (X0 : G) :  sK0 ≠ X0 := superpose step938 step10
  subsumption step1203 step938


@[equational_result]
theorem Finite.Equation677_and_Equation4314_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step9 step12
  have step26 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ X1) := superpose step12 step20
  have step33 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose step26 step12
  have step48 (X0 X1 : G) :  X0 = X1 := superpose step12 step33
  have step72 (X0 : G) :  sK0 ≠ X0 := superpose step48 step10
  subsumption step72 step48


@[equational_result]
theorem Finite.Equation677_and_Equation4325_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X3 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := superpose step9 step9
  have step24 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose step9 step11
  have step177 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X0 := superpose step24 step15
  have step178 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step24 step9
  have step230 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step177 step12
  have step231 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step178 step230
  have step302 (X0 X2 : G) :  X0 = X2 := superpose step231 step231
  have step460 (X0 : G) :  sK0 ≠ X0 := superpose step302 step10
  subsumption step460 step302


@[equational_result]
theorem Finite.Equation677_and_Equation4364_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 X2 X3 : G) :  (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose step9 step9
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step11
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := superpose step9 step12
  have step48 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step12 step9
  have step54 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step17 step48
  have step60 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step9 step42
  have step65 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step24 step54
  have step71 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step17 step60
  have step79 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose step65 step71
  have step87 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step65 step79
  have step94 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X0 := superpose step65 step87
  have step101 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step65 step94
  have step107 (X0 X1 : G) :  X0 = X1 := superpose step65 step101
  have step125 (X0 : G) :  sK0 ≠ X0 := superpose step107 step10
  subsumption step125 step107


@[equational_result]
theorem Finite.Equation677_and_Equation437_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step9
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step16 step21
  have step25 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step18
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step16 step11
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step16 step12
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step16 step27
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step25 step26
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step24 step9
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step31 step35
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step32 step36
  have step57 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ X0) := superpose step39 step25
  have step61 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose step25 step12
  have step78 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step32 step61
  have step81 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step39 step57
  have step902 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step78 step12
  have step1116 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step902 step902
  have step1231 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step22 step15
  have step1247 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose step1116 step1231
  have step1291 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X1)) := superpose step902 step1247
  have step1330 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X1)) := superpose step78 step1291
  have step1361 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step81 step1330
  have step1386 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step902 step1361
  have step1402 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step39 step1386
  have step1499 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step1402 step12
  have step1524 (X0 X1 : G) :  X0 = X1 := superpose step1402 step1499
  have step1737 (X0 : G) :  sK0 ≠ X0 := superpose step1524 step10
  subsumption step1737 step1524


@[equational_result]
theorem Finite.Equation677_and_Equation4388_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step9 step9
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step53 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step13 step11
  have step76 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step17 step13
  have step77 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step53 step76
  have step199 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step77 step11
  have step200 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step77 step199
  have step212 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step77 step200
  have step214 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step77 step212
  have step322 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step214 step12
  have step732 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step18 step12
  have step734 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose step322 step732
  have step4222 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X1 := superpose step734 step12
  have step4224 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X1) = X1 := superpose step20 step4222
  have step4276 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step53 step4224
  have step4321 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)) = X1 := superpose step4276 step19
  have step4347 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step4276 step322
  have step4431 (X0 X1 : G) :  X0 = X1 := superpose step4347 step4321
  have step4737 (X0 : G) :  sK0 ≠ X0 := superpose step4431 step10
  subsumption step4737 step4431


@[equational_result]
theorem Finite.Equation677_and_Equation4389_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X2 : G) :  ((X0 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ X2) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step37 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1))) = X1 := superpose step13 step12
  have step39 (X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose step19 step37
  have step61 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step39 step12
  have step63 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step61
  have step78 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose step18 step12
  have step139 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose step14 step63
  have step145 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step63 step12
  have step147 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step21 step145
  have step335 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step147 step12
  have step336 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose step147 step11
  have step337 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step18 step336
  have step338 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step147 step335
  have step341 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step78 step337
  have step342 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step338
  have step426 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step342 step14
  have step440 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose step342 step139
  have step460 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step341 step440
  have step472 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step342 step426
  have step492 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step460 step472
  have step499 (X0 X1 : G) :  X0 = X1 := superpose step460 step492
  have step631 (X0 : G) :  sK0 ≠ X0 := superpose step499 step10
  subsumption step631 step499


@[equational_result]
theorem Finite.Equation677_and_Equation4396_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose step9 step13
  have step15 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step14
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step28
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step15 step32
  have step36 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step18 step35
  have step40 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step36 step12
  have step45 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step40
  have step94 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose step45 step9
  have step171 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step11 step94
  have step182 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step94 step12
  have step198 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step94 step182
  have step209 (X0 X1 : G) :  X0 = X1 := superpose step171 step198
  have step264 (X0 : G) :  sK0 ≠ X0 := superpose step209 step10
  subsumption step264 step209


@[equational_result]
theorem Finite.Equation677_and_Equation440_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step30 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step19 step9
  have step35 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1)) := superpose step19 step12
  have step37 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) := superpose step9 step35
  have step278 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step37 step21
  have step358 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step30 step17
  have step363 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step11 step358
  have step395 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step20 step363
  have step415 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step278 step395
  have step443 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose step278 step12
  have step445 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step415 step443
  have step548 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step445 step11
  have step562 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step278 step548
  have step580 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step445 step24
  have step586 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step19 step24
  have step636 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step30 step586
  have step639 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step580
  have step666 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step30 step636
  have step687 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose step639 step666
  have step702 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose step639 step687
  have step715 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose step639 step702
  have step726 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := superpose step278 step715
  have step732 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X1 := superpose step562 step726
  have step736 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step639 step732
  have step830 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step736 step12
  have step852 (X0 X1 : G) :  X0 = X1 := superpose step736 step830
  have step1085 (X0 : G) :  sK0 ≠ X0 := superpose step852 step10
  subsumption step1085 step852


@[equational_result]
theorem Finite.Equation677_and_Equation4413_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X2) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X3 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose step9 step9
  have step27 (X0 X1 X2 : G) :  (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) := superpose step9 step12
  have step61 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X2))) = X2 := superpose step15 step12
  have step65 (X0 X2 : G) :  ((X0 ◇ X2) ◇ X0) = X2 := superpose step27 step61
  have step143 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step65 step12
  have step150 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step65 step143
  have step201 (X0 X2 : G) :  X0 = X2 := superpose step150 step150
  have step311 (X0 : G) :  sK0 ≠ X0 := superpose step201 step10
  subsumption step311 step201


@[equational_result]
theorem Finite.Equation677_and_Equation4433_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose step9 step13
  have step15 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step14
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X1)) = X0 := superpose step11 step9
  have step22 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) ◇ X1)) = X0 := superpose step9 step21
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step28
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step15 step32
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step35
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step9 step36
  have step45 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step18 step9
  have step46 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) := superpose step15 step45
  have step53 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0))) := superpose step9 step46
  have step60 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0))) := superpose step9 step53
  have step67 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step11 step60
  have step105 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step67 step12
  have step110 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step12 step105
  have step316 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step37 step12
  have step321 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step12 step316
  have step330 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step110 step321
  have step384 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := superpose step330 step9
  have step1478 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X0)) = X1 := superpose step384 step22
  have step1488 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step384 step12
  have step1502 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step12 step1488
  have step1511 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose step384 step1478
  have step1541 (X0 X1 : G) :  X0 = X1 := superpose step1502 step1511
  have step1680 (X0 : G) :  sK0 ≠ X0 := superpose step1541 step10
  subsumption step1680 step1541


@[equational_result]
theorem Finite.Equation677_and_Equation4445_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step215 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step20 step12
  have step258 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step215 step12
  have step267 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step258
  have step295 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step15 step22
  have step306 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step20 step22
  have step336 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step267 step306
  have step344 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose step12 step295
  have step354 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step9 step336
  have step360 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step267 step344
  have step368 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step215 step354
  have step377 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step360 step368
  have step384 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step12 step377
  have step391 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step267 step384
  have step464 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step391 step12
  have step486 (X0 X1 : G) :  X0 = X1 := superpose step391 step464
  have step691 (X0 : G) :  sK0 ≠ X0 := superpose step486 step10
  subsumption step691 step486


@[equational_result]
theorem Finite.Equation677_and_Equation4446_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose step9 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step424 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step23 step12
  have step443 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step424
  have step453 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step443
  have step480 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step453 step9
  have step483 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step453 step15
  have step499 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step453 step483
  have step502 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step453 step480
  have step513 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step453 step499
  have step517 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step502 step513
  have step677 (X0 X1 : G) :  X0 = X1 := superpose step517 step11
  have step909 (X0 : G) :  sK0 ≠ X0 := superpose step677 step10
  subsumption step909 step677


@[equational_result]
theorem Finite.Equation677_and_Equation4469_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step48 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step13 step12
  have step53 (X1 X2 : G) :  (X1 ◇ X1) = (X2 ◇ X2) := superpose step12 step48
  have step95 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step53 step12
  have step597 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step18 step12
  have step599 (X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) := superpose step95 step597
  have step4051 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step599 step12
  have step4053 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step20 step4051
  have step4082 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step4053
  have step4125 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1)) = X0 := superpose step4082 step18
  have step4153 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step4082 step95
  have step4250 (X0 X1 : G) :  X0 = X1 := superpose step4153 step4125
  have step4571 (X0 : G) :  sK0 ≠ X0 := superpose step4250 step10
  subsumption step4571 step4250


@[equational_result]
theorem Finite.Equation677_and_Equation4472_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1))) = X0 := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step22
  have step31 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))) := superpose step18 step11
  have step40 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step13 step9
  have step229 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step24 step18
  have step366 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step18 step19
  have step420 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step229 step9
  have step438 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step18 step420
  have step569 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step438 step19
  have step576 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) := superpose step366 step569
  have step592 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step31 step576
  have step601 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step366 step592
  have step607 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step601
  have step622 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0))) := superpose step40 step20
  have step703 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) := superpose step607 step622
  have step744 (X0 X1 : G) :  (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step607 step703
  have step774 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step12 step744
  have step877 (X0 X1 : G) :  X0 = X1 := superpose step774 step18
  have step1147 (X0 : G) :  sK0 ≠ X0 := superpose step877 step10
  subsumption step1147 step877


@[equational_result]
theorem Finite.Equation677_and_Equation4473_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)))) = X1 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1))) = X1 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step20
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step9 step19
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step13 step12
  have step36 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step13 step11
  have step41 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step35 step12
  have step82 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step35 step23
  have step93 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step9 step82
  have step97 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step93 step14
  have step98 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step93 step13
  have step100 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step93 step12
  have step104 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step13 step100
  have step106 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step98
  have step107 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step97
  have step110 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step41 step104
  have step111 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step106
  have step112 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step13 step107
  have step113 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step110 step111
  have step114 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step112
  have step115 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step36 step113
  have step116 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step114
  have step117 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step35 step116
  have step125 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose step13 step24
  have step167 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step117 step125
  have step193 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step117 step167
  have step213 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step9 step193
  have step226 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step117 step213
  have step235 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step9 step226
  have step241 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step115 step235
  have step245 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step117 step241
  have step253 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step117 step14
  have step276 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step117 step253
  have step285 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step245 step276
  have step495 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step285 step12
  have step504 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step245 step495
  have step524 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step504
  have step535 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step245 step524
  have step541 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step117 step535
  have step557 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X0)) := superpose step12 step18
  have step603 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X0) := superpose step541 step557
  have step631 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step541 step603
  have step656 (X0 X1 : G) :  X0 = X1 := superpose step541 step631
  have step728 (X0 : G) :  sK0 ≠ X0 := superpose step656 step10
  subsumption step728 step656


@[equational_result]
theorem Finite.Equation677_and_Equation4480_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := superpose step9 step17
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose step9 step12
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step23
  have step32 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step18 step29
  have step35 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step32 step12
  have step40 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step35
  have step80 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose step24 step12
  have step83 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step40 step80
  have step94 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step9 step83
  have step100 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step40 step94
  have step159 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose step18 step24
  have step166 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose step40 step159
  have step180 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step40 step166
  have step191 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step100 step180
  have step198 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step9 step191
  have step203 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step40 step198
  have step219 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step203 step12
  have step234 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step40 step219
  have step377 (X0 X1 : G) :  X0 = X1 := superpose step234 step203
  have step480 (X0 : G) :  sK0 ≠ X0 := superpose step377 step10
  subsumption step480 step377


@[equational_result]
theorem Finite.Equation677_and_Equation4583_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose step9 step12
  have step32 (X0 X1 : G) :  X0 = X1 := superpose step12 step25
  have step46 (X0 : G) :  sK0 ≠ X0 := superpose step32 step10
  subsumption step46 step32


@[equational_result]
theorem Finite.Equation677_and_Equation4584_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose step11 step9
  have step31 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X2 ◇ X1) := superpose step19 step19
  have step131 (X0 X1 X2 : G) :  (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose step31 step11
  have step168 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X1 := superpose step31 step17
  have step179 (X0 X1 : G) :  X0 = X1 := superpose step131 step168
  have step207 (X0 : G) :  sK0 ≠ X0 := superpose step179 step10
  subsumption step207 step179


@[equational_result]
theorem Finite.Equation677_and_Equation4587_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) = X1 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step20 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose step9 step11
  have step22 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step56 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)))) = X1 := superpose step13 step11
  have step71 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step20 step13
  have step72 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step20 step12
  have step74 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step20 step71
  have step80 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose step72 step72
  have step98 (X0 X1 X2 : G) :  ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose step72 step13
  have step118 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step17 step12
  have step122 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step23 step118
  have step204 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step11 step18
  have step206 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step18 step12
  have step242 (X0 X1 X2 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = ((X2 ◇ (X2 ◇ X1)) ◇ X2) := superpose step13 step23
  have step243 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step23
  have step259 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step72 step23
  have step266 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) := superpose step23 step13
  have step285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step11 step259
  have step540 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step204 step13
  have step593 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step22 step204
  have step595 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step22 step72
  have step614 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step540 step595
  have step615 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step98 step593
  have step642 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step540 step615
  have step651 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step80 step614
  have step652 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step614 step11
  have step659 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step614 step19
  have step672 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step285 step659
  have step676 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step642 step652
  have step679 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step540 step672
  have step710 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose step72 step25
  have step714 (X0 : G) :  (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step22 step25
  have step740 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step243 step714
  have step744 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ X0)) := superpose step651 step710
  have step754 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step676 step740
  have step755 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step744
  have step759 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step11 step754
  have step760 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step755
  have step763 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step759
  have step765 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step763
  have step767 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step98 step765
  have step768 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step760 step767
  have step782 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step768 step13
  have step786 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step768 step23
  have step787 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step768 step56
  have step790 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step768 step80
  have step808 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step768 step72
  have step813 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step679 step808
  have step901 (X0 X1 X2 : G) :  ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ X1) := superpose step74 step23
  have step949 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose step790 step901
  have step1000 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) := superpose step813 step949
  have step1112 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step23 step782
  have step1178 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose step782 step1112
  have step1262 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step122 step25
  have step1277 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step813 step1262
  have step1319 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step782 step1277
  have step1359 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step9 step1319
  have step1392 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step782 step1359
  have step1422 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1178 step1392
  have step1445 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step786 step1422
  have step1461 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1000 step1445
  have step1471 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step787 step1461
  have step1476 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step813 step1471
  have step1478 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step782 step1476
  have step1965 (X0 X1 X2 X3 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X0))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X2 := superpose step242 step74
  have step1968 (X0 X1 X2 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0))) ◇ (X2 ◇ (X2 ◇ X2))) = X2 := superpose step790 step1965
  have step2074 (X0 X1 X2 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) ◇ (X2 ◇ X2)) = X2 := superpose step813 step1968
  have step2171 (X0 X1 X2 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) = X2 := superpose step1478 step2074
  have step2229 (X0 X2 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) = X2 := superpose step782 step2171
  have step2273 (X0 X2 : G) :  ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) = X2 := superpose step1478 step2229
  have step2975 (X0 X1 X2 : G) :  ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)) := superpose step9 step266
  have step2987 (X0 X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (((X1 ◇ X3) ◇ X3) ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (((X1 ◇ X3) ◇ X3) ◇ (X1 ◇ X3)))) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X3) ◇ X3) ◇ (X1 ◇ X3)))) := superpose step266 step266
  have step3085 (X0 X1 X2 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)))) := superpose step266 step243
  have step3089 (X0 X1 X2 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (((X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2)))) := superpose step782 step3085
  have step3131 (X0 X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose step782 step2987
  have step3143 (X0 X1 X2 : G) :  ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose step23 step2975
  have step3172 (X0 X1 X2 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step1478 step3089
  have step3203 (X0 X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step1478 step3131
  have step3210 (X0 X1 X2 : G) :  ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)) := superpose step243 step3143
  have step3232 (X1 X2 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = (((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step782 step3172
  have step3256 (X0 X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step206 step3203
  have step3263 (X0 X1 X2 : G) :  ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)) := superpose step676 step3210
  have step3281 (X1 X2 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step1478 step3232
  have step3301 (X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step782 step3256
  have step3307 (X0 X1 X2 : G) :  (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) := superpose step11 step3263
  have step3315 (X1 X2 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step2273 step3281
  have step3330 (X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step23 step3301
  have step3336 (X0 X2 : G) :  (X0 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose step782 step3307
  have step3342 (X1 X2 : G) :  (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step790 step3315
  have step3352 (X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = (((X1 ◇ X1) ◇ X1) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step813 step3330
  have step3355 (X0 X2 : G) :  (X2 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose step1478 step3336
  have step3360 (X1 X2 : G) :  (X1 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose step813 step3342
  have step3367 (X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = ((X1 ◇ X1) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose step782 step3352
  have step3373 (X1 X2 : G) :  (X1 ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := superpose step3355 step3360
  have step3379 (X1 X2 X3 : G) :  ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ (X3 ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X3))) := superpose step3355 step3367
  have step3382 (X1 X2 : G) :  (X1 ◇ X1) = (X1 ◇ (X1 ◇ X2)) := superpose step3355 step3373
  have step3388 (X1 X2 X3 : G) :  ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X3)) = ((X1 ◇ X1) ◇ (X1 ◇ X3)) := superpose step3355 step3379
  have step3389 (X1 X2 : G) :  (X1 ◇ (X1 ◇ X2)) = X1 := superpose step1478 step3382
  have step3393 (X1 X2 X3 : G) :  (X1 ◇ (X1 ◇ X3)) = ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X3)) := superpose step1478 step3388
  have step3395 (X1 X3 : G) :  (X1 ◇ (X1 ◇ X3)) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose step782 step3393
  have step3396 (X1 X3 : G) :  (X1 ◇ X3) = (X1 ◇ (X1 ◇ X3)) := superpose step1478 step3395
  have step3397 (X1 X3 : G) :  (X1 ◇ X3) = X1 := superpose step3389 step3396
  have step3536 (X0 X1 : G) :  X0 = X1 := superpose step3397 step11
  have step3847 (X0 : G) :  sK0 ≠ X0 := superpose step3536 step10
  subsumption step3847 step3536


@[equational_result]
theorem Finite.Equation677_and_Equation4588_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := superpose step9 step9
  have step43 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) = (X0 ◇ X2) := superpose step11 step13
  have step56 (X0 X1 X2 : G) :  (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step13 step11
  have step62 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X0 ◇ X2) := superpose step56 step43
  have step141 (X0 X1 X2 : G) :  (X0 ◇ X1) = X2 := superpose step62 step11
  have step216 (X0 X2 : G) :  X0 = X2 := superpose step141 step12
  have step320 (X0 : G) :  sK0 ≠ X0 := superpose step216 step10
  subsumption step320 step216


@[equational_result]
theorem Finite.Equation677_and_Equation4606_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step29 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose step18 step18
  have step30 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step18
  have step33 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step18 step12
  have step37 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step13
  have step566 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step24
  have step567 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step24 step20
  have step595 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step30 step567
  have step613 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step9 step595
  have step629 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step613 step21
  have step639 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step566 step629
  have step646 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step639
  have step744 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step646 step613
  have step939 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step744 step12
  have step978 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step939
  have step1174 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose step978 step9
  have step1180 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := superpose step978 step20
  have step1186 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose step978 step29
  have step1188 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose step978 step33
  have step1238 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose step978 step1186
  have step1243 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose step1188 step1180
  have step1261 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step1174 step1243
  have step1266 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step1174 step1261
  have step1529 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step13 step37
  have step1606 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step978 step1529
  have step1668 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) = (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) := superpose step1174 step1606
  have step1729 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := superpose step978 step1668
  have step1786 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose step978 step1729
  have step1841 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose step978 step1786
  have step1888 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose step1238 step1841
  have step1925 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step978 step1888
  have step1957 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X1 := superpose step1266 step1925
  have step2049 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step1957 step11
  have step2074 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step1957 step37
  have step2075 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step978 step2074
  have step2097 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step978 step2049
  have step2135 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step978 step2075
  have step2153 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step1957 step2097
  have step2183 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step9 step2135
  have step2213 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step1174 step2183
  have step2232 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step2153 step2213
  have step2239 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step2153 step2232
  have step2242 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step9 step2239
  have step2244 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step2153 step2242
  have step2246 (X0 X1 : G) :  X0 = X1 := superpose step2153 step2244
  have step2490 (X0 : G) :  sK0 ≠ X0 := superpose step2246 step10
  subsumption step2490 step2246


@[equational_result]
theorem Finite.Equation677_and_Equation4612_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ X2) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 X3 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ X3) := superpose step9 step9
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step35 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose step12 step9
  have step145 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X2) ◇ X2) := superpose step23 step14
  have step148 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose step23 step9
  have step152 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = X0 := superpose step23 step148
  have step153 (X0 X2 : G) :  ((X0 ◇ X2) ◇ X2) = X0 := superpose step23 step145
  have step168 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step24 step24
  have step175 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step24 step12
  have step194 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step152 step175
  have step201 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step152 step168
  have step212 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step152 step194
  have step219 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step153 step201
  have step223 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose step212 step219
  have step225 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step212 step223
  have step232 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ X2) = (X0 ◇ X1) := superpose step212 step9
  have step249 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step153 step232
  have step285 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1))) = X1 := superpose step35 step12
  have step290 (X0 X1 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) = X1 := superpose step249 step285
  have step311 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step225 step290
  have step321 (X0 X1 : G) :  X0 = X1 := superpose step249 step311
  have step360 (X0 : G) :  sK0 ≠ X0 := superpose step321 step10
  subsumption step360 step321


@[equational_result]
theorem Finite.Equation677_and_Equation4629_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose step9 step12
  have step31 (X0 X1 : G) :  X0 = X1 := superpose step12 step25
  have step45 (X0 : G) :  sK0 ≠ X0 := superpose step31 step10
  subsumption step45 step31


@[equational_result]
theorem Finite.Equation677_and_Equation467_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ X) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (s ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step12 step12
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step10
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step10 step14
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step26 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step14
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step25
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step24 step29
  have step40 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step32 step19
  have step42 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step19 step14
  have step49 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step32 step42
  have step63 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) := superpose step17 step12
  have step66 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step12 step63
  have step77 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step19 step66
  have step91 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step66 step77
  have step94 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step49 step91
  have step120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step94 step13
  have step121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step40 step120
  have step127 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step94 step121
  have step134 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step13 step26
  have step167 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step66 step134
  have step186 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose step127 step167
  have step203 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step66 step186
  have step214 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose step66 step203
  have step218 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step127 step214
  have step221 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step127 step218
  have step276 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step18 step12
  have step287 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step127 step276
  have step317 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step127 step287
  have step341 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step66 step317
  have step360 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step66 step341
  have step376 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step127 step360
  have step388 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step221 step376
  have step398 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step127 step388
  have step405 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step127 step398
  have step420 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose step13 step405
  have step447 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose step405 step18
  have step453 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = X1 := superpose step12 step447
  have step471 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step66 step420
  have step474 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step127 step453
  have step485 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step127 step471
  have step494 (X0 X1 : G) :  X0 = X1 := superpose step474 step485
  have step596 (X0 : G) :  sK0 ≠ X0 := superpose step494 step11
  subsumption step596 step494


@[equational_result]
theorem Finite.Equation677_and_Equation4679_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 X3 : G) :  ((X0 ◇ X3) ◇ (X1 ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose step9 step9
  have step14 (X0 X1 X2 X3 : G) :  (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X1 ◇ X3) ◇ (X2 ◇ X0)) := superpose step9 step9
  have step22 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step34 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X1 := superpose step9 step12
  have step128 (X0 X1 X2 X3 X4 : G) :  (((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) = ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) := superpose step9 step13
  have step146 (X0 X1 X2 X3 : G) :  ((X0 ◇ X3) ◇ X2) = ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose step11 step13
  have step174 (X0 X1 X2 X3 : G) :  ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := superpose step13 step9
  have step175 (X0 X1 X2 X3 : G) :  ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose step13 step9
  have step205 (X0 X1 X2 X3 : G) :  ((X0 ◇ X3) ◇ X2) = ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X3))) := superpose step174 step146
  have step218 (X0 X1 X2 X3 X4 : G) :  ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X3) ◇ (X2 ◇ X0)) ◇ X4) := superpose step174 step128
  have step229 (X0 X1 X2 X3 : G) :  ((X0 ◇ X3) ◇ X2) = ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose step175 step205
  have step240 (X0 X1 X2 X3 X4 : G) :  ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4)) := superpose step174 step218
  have step252 (X0 X1 X2 X3 X4 : G) :  ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) := superpose step174 step240
  have step292 (X0 X1 X2 X3 : G) :  (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = (X0 ◇ (X3 ◇ X1)) := superpose step12 step14
  have step399 (X0 X1 X2 X3 : G) :  (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0)))) := superpose step175 step292
  have step460 (X0 X1 X2 X3 : G) :  (X0 ◇ (X3 ◇ X1)) = ((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0)))) := superpose step252 step399
  have step513 (X0 X1 X2 X3 : G) :  (X0 ◇ (X3 ◇ X1)) = ((X0 ◇ (X2 ◇ X1)) ◇ X3) := superpose step229 step460
  have step1012 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose step34 step513
  have step1038 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose step513 step12
  have step1045 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ (X3 ◇ X2)) := superpose step513 step9
  have step1079 (X0 X1 X2 X3 : G) :  ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3))) = X3 := superpose step513 step22
  have step1080 (X0 X1 X2 X3 : G) :  ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3)))) = X3 := superpose step174 step1079
  have step1114 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose step1045 step1038
  have step1130 (X0 X1 X2 : G) :  (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step1045 step1012
  have step1143 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3)))) = X3 := superpose step1045 step1080
  have step1189 (X0 X2 : G) :  (X0 ◇ X2) = X0 := superpose step1114 step1130
  have step1200 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X3))))) = X3 := superpose step174 step1143
  have step1244 (X0 X3 : G) :  X0 = X3 := superpose step1189 step1200
  have step1473 (X0 : G) :  sK0 ≠ X0 := superpose step1244 step10
  subsumption step1473 step1244


@[equational_result]
theorem Finite.Equation677_and_Equation473_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ ((Y ◇ X) ◇ (Y ◇ X)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (s ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (s ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step10 step14
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose step14 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step17 step14
  have step41 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step14 step39
  have step64 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step19 step10
  have step218 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) := superpose step64 step20
  have step228 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step64 step41
  have step229 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step10 step228
  have step235 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose step10 step218
  have step240 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step229 step235
  have step351 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step240 step41
  have step433 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X1) = (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))))) := superpose step15 step24
  have step434 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X1) := superpose step12 step433
  have step469 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ X1) := superpose step351 step434
  have step502 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step10 step469
  have step579 (X0 X1 : G) :  X0 = X1 := superpose step502 step13
  have step795 (X0 : G) :  sK0 ≠ X0 := superpose step579 step11
  subsumption step795 step579


@[equational_result]
theorem Finite.Equation677_and_Equation50_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation50 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step35 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step16 step12
  have step37 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step35
  have step43 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step37 step37
  have step121 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose step43 step37
  have step234 (X0 X2 : G) :  (X0 ◇ X0) = X2 := superpose step121 step11
  have step266 (X0 X2 : G) :  X0 = X2 := superpose step234 step234
  have step426 (X0 : G) :  sK0 ≠ X0 := superpose step266 step10
  subsumption step426 step266


@[equational_result]
theorem Finite.Equation677_and_Equation56_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation56 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X1 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step28 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step18 step18
  have step60 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step28 step20
  have step176 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step60 step17
  have step198 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step60 step176
  have step223 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose step198 step9
  have step224 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step198 step15
  have step235 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step198 step60
  have step239 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step198 step235
  have step243 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step198 step224
  have step244 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step198 step223
  have step246 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose step239 step243
  have step247 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step244 step246
  have step322 (X0 X2 : G) :  X0 = X2 := superpose step247 step247
  have step533 (X0 : G) :  sK0 ≠ X0 := superpose step322 step10
  subsumption step533 step322


@[equational_result]
theorem Finite.Equation677_and_Equation615_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step11 step9
  have step23 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step19
  have step31 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step44 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step23 step31
  have step49 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step23 step44
  have step50 (X0 X1 : G) :  X0 = X1 := superpose step23 step49
  have step69 (X0 : G) :  sK0 ≠ X0 := superpose step50 step10
  subsumption step69 step50


@[equational_result]
theorem Finite.Equation677_and_Equation616_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step11 step9
  have step27 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step18 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step46 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step27 step12
  have step50 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step46
  have step60 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = X0 := superpose step50 step12
  have step84 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step27 step28
  have step112 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose step60 step84
  have step123 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step50 step112
  have step128 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step123 step50
  have step159 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X1))) := superpose step28 step15
  have step173 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X1)) := superpose step128 step159
  have step178 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step128 step173
  have step181 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose step128 step178
  have step182 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose step128 step181
  have step183 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step128 step182
  have step184 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step128 step183
  have step214 (X0 X1 : G) :  X0 = X1 := superpose step184 step11
  have step345 (X0 : G) :  sK0 ≠ X0 := superpose step214 step10
  subsumption step345 step214


@[equational_result]
theorem Finite.Equation677_and_Equation619_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose step9 step13
  have step18 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose step18 step18
  have step31 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step18 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step31
  have step60 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose step34 step11
  have step66 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose step34 step12
  have step149 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step18 step19
  have step179 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step149
  have step249 (X0 X1 X2 : G) :  ((X2 ◇ X0) ◇ X0) = (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) := superpose step24 step11
  have step459 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step60 step12
  have step514 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) := superpose step14 step19
  have step540 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) := superpose step459 step514
  have step546 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step249 step540
  have step1382 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step546 step12
  have step1432 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ X0) := superpose step179 step1382
  have step1541 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step1432 step11
  have step1548 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1432 step12
  have step1554 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step1432 step19
  have step1574 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step66 step1554
  have step1577 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step12 step1548
  have step1600 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step1541 step1574
  have step2800 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step19 step1577
  have step2869 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step1577 step19
  have step2924 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step1577 step2869
  have step2959 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step1577 step2800
  have step2977 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step1432 step2924
  have step3001 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step1600 step2977
  have step3237 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step22 step3001
  have step3332 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step3001 step1577
  have step3333 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step3001 step3332
  have step3387 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step2959 step3237
  have step3423 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose step3333 step3387
  have step3446 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step3001 step3423
  have step3457 (X0 X1 : G) :  X0 = X1 := superpose step3333 step3446
  have step3683 (X0 : G) :  sK0 ≠ X0 := superpose step3457 step10
  subsumption step3683 step3457


@[equational_result]
theorem Finite.Equation677_and_Equation620_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step20
  have step26 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step17
  have step27 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step24
  have step34 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step21 step12
  have step37 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose step26 step34
  have step40 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose step27 step37
  have step43 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step27 step12
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step43
  have step64 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step26 step26
  have step71 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step26 step11
  have step96 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step27 step71
  have step101 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step27 step64
  have step111 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step48 step96
  have step113 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step21 step101
  have step121 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step111 step113
  have step127 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step27 step121
  have step132 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step40 step127
  have step133 (X0 X1 : G) :  X0 = X1 := superpose step111 step132
  have step157 (X0 : G) :  sK0 ≠ X0 := superpose step133 step10
  subsumption step157 step133


@[equational_result]
theorem Finite.Equation677_and_Equation629_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step9 step9
  have step16 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step16
  have step34 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step16
  have step35 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step27 step9
  have step47 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step27 step17
  have step60 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step17 step12
  have step74 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step35 step60
  have step85 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step34 step47
  have step94 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step27 step74
  have step104 (X0 X1 : G) :  X0 = X1 := superpose step85 step94
  have step134 (X0 : G) :  sK0 ≠ X0 := superpose step104 step10
  subsumption step134 step104


@[equational_result]
theorem Finite.Equation677_and_Equation632_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  X0 = X1 := superpose step11 step9
  have step39 (X0 : G) :  sK0 ≠ X0 := superpose step17 step10
  subsumption step39 step17


@[equational_result]
theorem Finite.Equation677_and_Equation66_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation66 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step10
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step10 step13
  have step24 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step22
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step24 step12
  have step41 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step12
  have step42 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step16 step41
  have step47 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ X0) := superpose step27 step42
  have step50 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step24 step47
  have step62 (X0 X1 : G) :  X0 = X1 := superpose step50 step13
  have step111 (X0 : G) :  sK0 ≠ X0 := superpose step62 step11
  subsumption step111 step62


@[equational_result]
theorem Finite.Equation677_and_Equation676_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step51 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose step19 step14
  have step54 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step14 step51
  have step75 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) = X0 := superpose step54 step14
  have step80 (X0 X1 : G) :  X0 = X1 := superpose step14 step75
  have step126 (X0 : G) :  sK0 ≠ X0 := superpose step80 step11
  subsumption step126 step80


@[equational_result]
theorem Finite.Equation677_and_Equation818_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose step11 step9
  have step20 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step20 step19
  have step36 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step39 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step21 step36
  have step44 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step20 step39
  have step50 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step11 step21
  have step65 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) = X1 := superpose step11 step44
  have step85 (X0 X1 : G) :  X0 = X1 := superpose step50 step65
  have step110 (X0 : G) :  sK0 ≠ X0 := superpose step85 step10
  subsumption step110 step85


@[equational_result]
theorem Finite.Equation677_and_Equation819_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step28 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose step17 step20
  have step30 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step17 step28
  have step32 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step17 step30
  have step47 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step32 step12
  have step52 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step32 step47
  have step75 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step52 step12
  have step76 (X0 X1 : G) :  X0 = X1 := superpose step52 step75
  have step129 (X0 : G) :  sK0 ≠ X0 := superpose step76 step10
  subsumption step129 step76


@[equational_result]
theorem Finite.Equation677_and_Equation820_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step13 step11
  have step19 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step16
  have step28 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step41 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := superpose step19 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step19 step41
  have step45 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step13 step44
  have step53 (X0 X1 : G) :  X0 = X1 := superpose step45 step11
  have step92 (X0 : G) :  sK0 ≠ X0 := superpose step53 step10
  subsumption step92 step53


@[equational_result]
theorem Finite.Equation677_and_Equation822_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step13 step11
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose step11 step9
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step18 step16
  have step21 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step19 step13
  have step25 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step38 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step25
  have step41 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X0 := superpose step19 step38
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step11 step41
  have step86 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step53 step12
  have step89 (X0 X1 : G) :  X0 = X1 := superpose step41 step86
  have step135 (X0 : G) :  sK0 ≠ X0 := superpose step89 step10
  subsumption step135 step89


@[equational_result]
theorem Finite.Equation677_and_Equation823_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step16 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step13 step11
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step11 step9
  have step19 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step16
  have step20 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step18 step15
  have step21 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step18 step20
  have step22 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step19 step21
  have step27 (X0 X1 : G) :  X0 = X1 := superpose step22 step11
  have step59 (X0 : G) :  sK0 ≠ X0 := superpose step27 step10
  subsumption step59 step27


@[equational_result]
theorem Finite.Equation677_and_Equation832_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step20
  have step24 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step18
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step9
  have step52 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step12 step24
  have step59 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X0 := superpose step30 step24
  have step64 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step24 step12
  have step71 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step24 step64
  have step76 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step30 step52
  have step79 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step30 step71
  have step98 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step19 step19
  have step111 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) := superpose step19 step24
  have step117 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step19 step24
  have step124 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step30 step117
  have step129 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step30 step111
  have step139 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step59 step98
  have step143 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step59 step124
  have step147 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := superpose step59 step129
  have step153 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step76 step139
  have step156 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step79 step147
  have step158 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step143 step153
  have step160 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step156 step158
  have step161 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step156 step160
  have step162 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step156 step161
  have step163 (X0 X1 : G) :  X0 = X1 := superpose step156 step162
  have step193 (X0 : G) :  sK0 ≠ X0 := superpose step163 step10
  subsumption step193 step163


@[equational_result]
theorem Finite.Equation677_and_Equation835_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step13 step14
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose step9 step17
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ X0) := superpose step12 step18
  have step29 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X0) := superpose step18 step18
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step9
  have step34 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step30 step29
  have step35 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step30 step28
  have step38 (X0 X1 : G) :  X0 = X1 := superpose step34 step35
  have step63 (X0 : G) :  sK0 ≠ X0 := superpose step38 step10
  subsumption step63 step38


@[equational_result]
theorem Finite.Equation677_and_Equation842_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step16 step16
  have step36 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step22
  have step37 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step19
  have step39 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step16 step19
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step39
  have step44 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step16 step37
  have step45 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step36 step44
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step43 step45
  have step50 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step46 step11
  have step69 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step13 step11
  have step70 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step69
  have step74 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step16 step70
  have step78 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step50 step74
  have step86 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step78 step16
  have step99 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose step78 step86
  have step107 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X0) := superpose step78 step99
  have step109 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step78 step107
  have step114 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step17 step17
  have step143 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step109 step114
  have step159 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose step109 step143
  have step171 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step109 step159
  have step177 (X0 X1 : G) :  X0 = X1 := superpose step109 step171
  have step215 (X0 : G) :  sK0 ≠ X0 := superpose step177 step10
  subsumption step215 step177


@[equational_result]
theorem Finite.Equation677_and_Equation846_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step20
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X1 := superpose step24 step9
  have step78 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step27 step12
  have step93 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step78
  have step125 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step93 step18
  have step128 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step93 step27
  have step136 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose step27 step125
  have step137 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step27 step136
  have step138 (X0 X1 : G) :  X0 = X1 := superpose step128 step137
  have step197 (X0 : G) :  sK0 ≠ X0 := superpose step138 step10
  subsumption step197 step138


@[equational_result]
theorem Finite.Equation677_and_Equation870_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ X)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ s) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose step10 step10
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step19 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose step13 step10
  have step21 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step26 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) := superpose step14 step10
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step14 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step12 step12
  have step113 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step21 step21
  have step115 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step15 step21
  have step154 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step115
  have step164 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step33 step154
  have step167 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step13 step164
  have step199 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step167
  have step212 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step24 step199
  have step225 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step167 step33
  have step258 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step212 step225
  have step267 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step19 step258
  have step270 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step33 step267
  have step274 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step270 step14
  have step275 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step270 step19
  have step277 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step270 step13
  have step291 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step21 step275
  have step295 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step277 step291
  have step299 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step274 step295
  have step320 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step270 step22
  have step361 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step299 step320
  have step372 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step277 step361
  have step377 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step274 step372
  have step385 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step377 step10
  have step390 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose step377 step21
  have step644 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))) := superpose step17 step34
  have step649 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))) := superpose step113 step644
  have step680 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step377 step649
  have step704 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step377 step680
  have step723 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step390 step704
  have step732 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step14 step723
  have step1038 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose step385 step15
  have step1043 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step385 step22
  have step1055 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step14 step1043
  have step1059 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step377 step1038
  have step1087 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step732 step1059
  have step1106 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose step377 step1087
  have step1260 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step1055 step385
  have step1261 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1106 step1260
  have step1306 (X0 X1 : G) :  (X1 ◇ X0) = X0 := superpose step385 step1261
  have step1392 (X0 X1 : G) :  ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose step19 step26
  have step1453 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose step1306 step1392
  have step1486 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = X0 := superpose step1306 step1453
  have step1512 (X0 X1 : G) :  X0 = X1 := superpose step1306 step1486
  have step1621 (X0 : G) :  sK0 ≠ X0 := superpose step1512 step11
  subsumption step1621 step1512


@[equational_result]
theorem Finite.Equation677_and_Equation872_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ X)) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ s) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step23 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step14 step10
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step23 step14
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step14 step12
  have step46 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step26 step13
  have step64 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step26 step19
  have step86 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step46 step64
  have step91 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step86
  have step97 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step91 step10
  have step274 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step97 step34
  have step275 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step19 step274
  have step290 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step14 step275
  have step418 (X0 X1 : G) :  (X0 ◇ X1) = X0 := superpose step97 step290
  have step420 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = X0 := superpose step14 step290
  have step439 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step290 step34
  have step465 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step91 step439
  have step482 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step420 step465
  have step490 (X0 X1 : G) :  X0 = X1 := superpose step418 step482
  have step584 (X0 : G) :  sK0 ≠ X0 := superpose step490 step11
  subsumption step584 step490


@[equational_result]
theorem Finite.Equation677_and_Equation873_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ sK1 := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ (Y ◇ (X ◇ (Y ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ s) ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step36 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step11 step13
  have step38 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose step13 step11
  have step41 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ X0) := superpose step13 step14
  have step121 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step20 step36
  have step130 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step28 step121
  have step146 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step130
  have step167 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose step146 step20
  have step179 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step146 step14
  have step184 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step146 step179
  have step195 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step146 step167
  have step208 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ X0) := superpose step184 step195
  have step210 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step146 step208
  have step236 (X0 X1 X2 : G) :  ((X2 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose step41 step38
  have step250 (X1 X2 : G) :  (X2 ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose step210 step236
  have step273 (X1 X2 : G) :  X1 = X2 := superpose step210 step250
  have step337 (X0 : G) :  sK0 ≠ X0 := superpose step273 step12
  subsumption step337 step273


@[equational_result]
theorem Finite.Equation677_and_Equation879_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ ((Y ◇ X) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose step13 step10
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step14 step12
  have step121 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step19 step12
  have step171 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step21 step10
  have step217 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step171 step19
  have step230 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step121 step217
  have step264 (X0 X1 : G) :  (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X1 := superpose step26 step18
  have step275 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose step26 step18
  have step300 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0)) = X1 := superpose step230 step275
  have step310 (X0 X1 : G) :  (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step230 step264
  have step336 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose step230 step300
  have step344 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step10 step310
  have step362 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose step14 step336
  have step377 (X0 X1 : G) :  X0 = X1 := superpose step344 step362
  have step447 (X0 : G) :  sK0 ≠ X0 := superpose step377 step11
  subsumption step447 step377


