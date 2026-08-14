import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import equational_theories.Finite677.Eq19855
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation677_and_Equation102_implies_Equation160 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation102 G) : Equation160 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step9
  have step14 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step13
  have step16 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step14 step10
  have step26 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step9 step26
  have step44 : sK0 ≠ sK0 := superpose step33 step16
  subsumption step44 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1023_implies_Equation1322 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1023 G) : Equation1322 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step11
  have step51 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step17 step12
  have step56 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step51
  have step62 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step30 step56
  have step65 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step30 step62
  have step67 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose step30 step10
  have step89 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step12 step18
  have step91 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step18
  have step101 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose step18 step11
  have step116 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose step30 step101
  have step122 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose step30 step91
  have step123 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step30 step89
  have step134 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose step30 step116
  have step138 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step30 step122
  have step139 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step30 step123
  have step148 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose step30 step134
  have step152 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step30 step139
  have step207 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step138 step138
  have step343 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step65 step19
  have step345 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step11 step343
  have step751 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step15 step138
  have step752 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step345 step751
  have step794 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step11 step752
  have step902 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step794 step12
  have step2074 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step207 step19
  have step2096 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step902 step2074
  have step2138 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step12 step2096
  have step2169 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step138 step2138
  have step2387 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step2169 step148
  have step2756 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose step11 step2387
  have step2886 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose step65 step152
  have step2977 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step902 step2886
  have step3017 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step2756 step2977
  have step3044 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step11 step3017
  have step3107 : sK0 ≠ sK0 := superpose step3044 step67
  subsumption step3107 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1026_implies_Equation1851 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1026 G) : Equation1851 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step18
  have step57 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step9
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step57 step56
  have step72 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step66 step11
  have step91 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step66 step19
  have step104 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step66 step91
  have step112 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step72 step104
  have step133 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose step112 step10
  have step134 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose step18 step133
  subsumption step134 step57


@[equational_result]
theorem Finite.Equation677_and_Equation1029_implies_Equation1226 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1029 G) : Equation1226 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step19 (X0 X1 X2 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ (X2 ◇ X2)) ◇ X2) := superpose step15 step15
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step15 step12
  have step27 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step15 step12
  have step29 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step27
  have step31 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step17 step9
  have step45 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step20 step16
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step45
  have step188 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose step56 step19
  have step194 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step56 step16
  have step195 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step56 step12
  have step197 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step56 step194
  have step256 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step29
  have step257 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step56 step29
  have step297 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step197 step257
  have step323 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step188 step15
  have step342 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step195 step323
  have step390 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step342 step12
  have step392 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step56 step390
  have step494 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step342 step31
  have step496 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step31 step18
  have step506 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step342 step496
  have step508 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step17 step494
  have step512 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step20 step506
  have step516 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step256 step512
  have step518 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step508 step516
  have step519 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step297 step518
  have step520 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step392 step519
  have step523 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step520 step56
  have step539 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step520 step12
  have step542 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step16 step539
  have step551 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step523 step542
  have step554 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step520 step551
  have step700 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step554 step10
  have step701 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step554 step9
  subsumption step700 step701


@[equational_result]
theorem Finite.Equation677_and_Equation1039_implies_Equation1045 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1039 G) : Equation1045 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose step11 step18
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step12
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step33 step9
  have step49 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step29 step48
  have step52 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step49
  have step71 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step52 step18
  have step74 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose step52 step71
  have step80 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step52 step74
  have step143 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step11 step80
  have step148 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step80 step80
  have step158 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step80 step11
  have step175 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step148 step143
  have step184 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose step158 step175
  have step338 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step148 step80
  have step601 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose step19 step338
  have step653 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose step148 step601
  have step673 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X1 := superpose step184 step653
  have step685 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step338 step673
  have step1027 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step685 step10
  subsumption step1027 step685


@[equational_result]
theorem Finite.Equation677_and_Equation1045_implies_Equation1075 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1045 G) : Equation1075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ X1) := superpose step18 step18
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step12
  have step32 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1)) := superpose step18 step12
  have step36 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) := superpose step9 step32
  have step44 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step18 step26
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step11 step44
  have step130 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = ((X2 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) := superpose step11 step24
  have step135 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step16 step24
  have step168 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step63 step135
  have step180 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step130 step168
  have step186 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step26 step180
  have step207 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)))) := superpose step14 step9
  have step220 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step36 step207
  have step236 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1)) = X1 := superpose step186 step220
  have step245 (X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X1 := superpose step9 step236
  have step252 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose step245 step24
  have step297 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step245 step15
  have step329 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose step19 step297
  have step354 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step18 step329
  have step373 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step186 step354
  have step383 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step186 step373
  have step391 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step186 step383
  have step413 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step391 step18
  have step419 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step245 step413
  have step955 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step419 step19
  have step964 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step252 step955
  have step999 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step391 step964
  have step1018 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step245 step999
  have step1229 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step1018 step419
  have step1230 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step391 step1229
  have step1272 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step1018 step1230
  have step1428 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step1272 step10
  subsumption step1428 step1272


@[equational_result]
theorem Finite.Equation677_and_Equation1075_implies_Equation1086 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1075 G) : Equation1086 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (s ◇ Y)) ◇ s)) := by
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
  have step15 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose step10 step10
  have step18 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step13 step10
  have step20 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step36 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step12 step14
  have step49 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step12 step36
  have step66 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) = X1 := superpose step13 step15
  have step88 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step20 step66
  have step98 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) = X1 := superpose step49 step88
  have step103 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step13 step98
  have step108 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step14 step103
  have step109 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step18 step103
  have step127 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step109
  have step128 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step103 step108
  have step180 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step127 step11
  have step181 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step128 step180
  subsumption step181 step103


@[equational_result]
theorem Finite.Equation677_and_Equation1086_implies_Equation1122 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1086 G) : Equation1122 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) := by
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
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose step13 step13
  have step23 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose step13 step15
  have step26 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step29 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step13 step16
  have step30 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step37 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step13 step32
  have step43 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step37 step13
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step43
  have step109 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose step44 step12
  have step111 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose step44 step26
  have step113 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step44 step14
  have step114 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step44 step13
  have step115 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step44 step11
  have step127 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step44 step109
  have step134 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step26 step18
  have step141 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step44 step18
  have step176 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step44 step141
  have step183 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) := superpose step44 step134
  have step205 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose step44 step183
  have step222 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step176 step205
  have step231 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step44 step222
  have step238 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0))) := superpose step11 step29
  have step241 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step15 step29
  have step269 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step111 step241
  have step272 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = ((X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) := superpose step111 step238
  have step287 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose step176 step269
  have step290 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step44 step272
  have step301 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step176 step287
  have step304 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step44 step290
  have step312 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step231 step301
  have step318 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step44 step312
  have step320 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X1) := superpose step304 step318
  have step868 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (X0 ◇ X0))) := superpose step23 step30
  have step870 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step23 step114
  have step871 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose step176 step870
  have step873 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step16 step868
  have step901 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step320 step871
  have step903 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step176 step873
  have step928 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step44 step901
  have step930 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step44 step903
  have step952 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step115 step928
  have step953 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step320 step930
  have step970 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step952 step953
  have step983 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step176 step970
  have step993 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step115 step983
  have step1034 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step993 step113
  have step1490 : sK0 ≠ sK0 := superpose step1034 step127
  subsumption step1490 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1098_implies_Equation3091 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1098 G) : Equation3091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step12 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK2) ◇ sK1) ◇ sK2) := mod_symm nh
  have step14 (X Y Z : G) : (((Y ◇ X) ◇ (Z ◇ Y)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ Y)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Z ◇ Y)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step29 (X0 X1 X2 X3 : G) :  ((X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) ◇ X3) = X2 := superpose step14 step14
  have step34 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X2 ◇ (X1 ◇ X0)) ◇ X1) := superpose step14 step14
  have step45 (X0 X1 X2 : G) :  (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose step34 step29
  have step384 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose step34 step14
  have step2722 : sK0 ≠ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) ◇ sK2) := superpose step384 step12
  subsumption step2722 step45


@[equational_result]
theorem Finite.Equation677_and_Equation1113_implies_Equation2534 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1113 G) : Equation2534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step11 step12


@[equational_result]
theorem Finite.Equation677_and_Equation1117_implies_Equation2538 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1117 G) : Equation2538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step11 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK2) := mod_symm nh
  have step12 (X Y Z : G) : ((Y ◇ ((Y ◇ X) ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ s) ◇ Z))) (fun s => (s ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step11 step12


@[equational_result]
theorem Finite.Equation677_and_Equation1122_implies_Equation1184 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1122 G) : Equation1184 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ Y)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step24 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose step12 step13
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step13 step10
  have step44 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose step28 step13
  have step47 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step10 step44
  have step402 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) := superpose step28 step24
  have step447 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step12 step402
  have step463 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step12 step447
  have step474 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step47 step463
  have step482 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step474 step12
  have step1020 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step482 step11
  subsumption step1020 step482


@[equational_result]
theorem Finite.Equation677_and_Equation118_implies_Equation127 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation118 G) : Equation127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step13 step13
  have step28 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step14 step15
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step15
  have step38 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step15 step28
  have step42 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step19 step38
  have step79 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step30 step12
  have step100 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step11 step42
  have step178 : sK0 ≠ sK0 := superpose step100 step79
  subsumption step178 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1184_implies_Equation1229 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1184 G) : Equation1229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step13 (X Z Y : G) : ((Z ◇ (Z ◇ Y)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ (Z ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Z ◇ (Z ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step31 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose step14 step13
  have step54 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step13 step15
  have step55 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step31
  have step61 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step55
  have step90 : sK0 ≠ (sK0 ◇ sK0) := superpose step54 step12
  subsumption step90 step61


@[equational_result]
theorem Finite.Equation677_and_Equation1226_implies_Equation1231 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1226 G) : Equation1231 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1))) = X0 := superpose step9 step9
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step13
  have step21 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step12 step9
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step14 step26
  have step29 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose step22 step21
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step28
  have step54 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step30 step29
  have step83 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step54 step10
  subsumption step83 step14


@[equational_result]
theorem Finite.Equation677_and_Equation1229_implies_Equation1242 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1229 G) : Equation1242 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step16 step12
  have step78 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step19 step11
  have step82 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step19 step16
  have step83 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step42 step82
  have step86 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step78 step83
  have step88 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step86
  have step91 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step88 step11
  have step174 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step91 step11
  have step177 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step91 step17
  have step634 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step11 step177
  have step638 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step177 step177
  have step4265 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose step638 step12
  have step4305 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X1 := superpose step18 step4265
  have step4913 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step4305 step177
  have step5534 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step4305 step4913
  have step5575 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose step4913 step634
  have step5579 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose step638 step5575
  have step5646 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step5534 step5579
  have step6532 : sK0 ≠ (sK0 ◇ sK0) := superpose step5646 step10
  subsumption step6532 step174


@[equational_result]
theorem Finite.Equation677_and_Equation1231_implies_Equation1455 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1231 G) : Equation1455 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0)) = X0 := superpose step9 step9
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step13
  have step15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step14 step10
  have step22 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step23 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step14 step12
  have step29 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose step23 step22
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step25 step14
  have step32 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step25 step11
  have step35 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step32
  have step38 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step30 step35
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step38
  have step205 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step29 step24
  have step228 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step39 step205
  have step238 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step29 step228
  have step246 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step39 step238
  have step251 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step14 step246
  have step278 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) := superpose step251 step11
  have step287 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step39 step278
  have step301 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step9 step287
  have step452 : sK0 ≠ sK0 := superpose step301 step15
  subsumption step452 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1232_implies_Equation2064 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1232 G) : Equation2064 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step13
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step14
  have step17 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := superpose step15 step10
  have step27 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step35 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step15 step27
  have step38 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ X0) := superpose step15 step35
  have step40 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step15 step38
  have step50 : sK0 ≠ sK0 := superpose step40 step17
  subsumption step50 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1239_implies_Equation1895 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1239 G) : Equation1895 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0)) := superpose step9 step9
  have step14 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step13
  have step15 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := superpose step14 step15
  have step19 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step9 step18
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step19 step19
  have step33 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step19 step12
  have step102 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step29 step12
  have step306 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step19 step21
  have step315 (X0 X1 : G) :  (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step21 step19
  have step336 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose step102 step315
  have step405 (X0 X1 : G) :  (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step336 step21
  have step410 (X0 X1 : G) :  (X0 ◇ X1) = (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step12 step405
  have step432 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step306 step410
  have step567 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X1)) := superpose step21 step432
  have step574 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step432 step11
  have step593 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) := superpose step102 step567
  have step606 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step432 step593
  have step613 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step574 step606
  have step1101 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step613 step21
  have step1170 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step613 step1101
  have step1210 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step613 step1170
  have step1235 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step574 step1210
  have step1677 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step613 step33
  have step1725 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose step1235 step1677
  have step1928 : sK0 ≠ sK0 := superpose step1725 step10
  subsumption step1928 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation206 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation206 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step739 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step12 step625
  have step932 : sK0 ≠ sK0 := superpose step739 step11
  subsumption step932 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1242_implies_Equation1279 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1242 G) : Equation1279 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step11 step9
  have step17 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step160 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step13 step11
  have step187 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step160
  have step202 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step17 step187
  have step210 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step202 step11
  have step367 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step210 step10
  have step583 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step12
  have step601 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose step202 step583
  have step1763 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step601 step11
  have step2196 : sK0 ≠ sK0 := superpose step1763 step367
  subsumption step2196 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation127_implies_Equation167 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation127 G) : Equation167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step13
  have step35 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step22 step10
  have step64 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step35 step14
  have step115 : sK0 ≠ sK0 := superpose step64 step11
  subsumption step115 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1279_implies_Equation1325 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1279 G) : Equation1325 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step15 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : ((((Y ◇ X) ◇ (Y ◇ X)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ s) ◇ Y) ◇ Y)) := by
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
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step17
  have step24 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step17 step16
  have step28 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step22 step12
  have step32 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := superpose step22 step13
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step28
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step17 step18
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step22 step39
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step34 step45
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step34 step47
  have step53 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose step15 step15
  have step54 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose step15 step18
  have step56 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))))) = X1 := superpose step15 step17
  have step57 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose step48 step56
  have step59 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step48 step54
  have step60 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ X1) := superpose step48 step53
  have step66 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step48 step60
  have step69 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step48 step12
  have step77 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step48 step32
  have step185 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step66 step17
  have step256 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step48 step24
  have step308 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step66 step256
  have step460 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose step57 step69
  have step461 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step185 step460
  have step526 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step185 step57
  have step612 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X1 := superpose step24 step59
  have step622 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step59 step16
  have step635 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step66 step622
  have step643 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) = X1 := superpose step66 step612
  have step666 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step461 step635
  have step673 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step308 step643
  have step694 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X1 ◇ X0) := superpose step526 step666
  have step700 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step17 step673
  have step717 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := superpose step48 step694
  have step723 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step48 step700
  have step739 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step717 step723
  have step797 : sK0 ≠ sK0 := superpose step739 step77
  subsumption step797 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1289_implies_Equation2507 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1289 G) : Equation2507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step14 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step13 step14


@[equational_result]
theorem Finite.Equation677_and_Equation1316_implies_Equation2940 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1316 G) : Equation2940 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step16 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step13 step16


@[equational_result]
theorem Finite.Equation677_and_Equation1322_implies_Equation1648 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1322 G) : Equation1648 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ Y) ◇ s) ◇ s)) := by
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
  have step20 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step13
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step34 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step22 step14
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step22 step10
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step22 step35
  have step44 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step40 step10
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step40 step12
  have step74 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0)) := superpose step14 step20
  have step79 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step40 step20
  have step102 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step44 step74
  have step106 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step79 step102
  have step187 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step49 step106
  have step203 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step34 step187
  have step272 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step203 step10
  have step273 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step203 step12
  have step274 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step203 step20
  have step532 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step272 step272
  have step539 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step272
  have step577 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step203 step539
  have step830 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step273
  have step3969 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose step577 step27
  have step3981 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step274 step3969
  have step4060 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step273 step3981
  have step4471 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step532 step830
  have step4617 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step4060 step4471
  have step4656 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step272 step4617
  have step6279 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step4656 step273
  have step6296 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step273 step6279
  have step6687 : sK0 ≠ sK0 := superpose step6296 step11
  subsumption step6687 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1325_implies_Equation1434 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1325 G) : Equation1434 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step13 step10
  have step37 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step54 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step25 step14
  have step59 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step37 step54
  have step61 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step59
  have step68 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose step61 step10
  have step74 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step61 step11
  have step79 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step61 step68
  have step187 : sK0 ≠ (sK0 ◇ sK0) := superpose step79 step74
  subsumption step187 step61


@[equational_result]
theorem Finite.Equation677_and_Equation1434_implies_Equation1525 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1434 G) : Equation1525 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step28 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step25 step25
  have step87 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose step28 step9
  have step91 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step14 step12
  have step95 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step91
  have step96 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step87 step95
  have step97 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step96 step11
  have step183 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose step97 step28
  have step186 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose step97 step10
  have step187 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step97 step186
  have step190 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step97 step183
  have step328 (X0 : G) :  sK0 ≠ (X0 ◇ (X0 ◇ sK0)) := superpose step28 step187
  subsumption step328 step190


@[equational_result]
theorem Finite.Equation677_and_Equation1451_implies_Equation1657 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1451 G) : Equation1657 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose step11 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step64 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step17
  have step87 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step64 step11
  have step161 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step87 step9
  have step179 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := superpose step87 step10
  have step443 : sK0 ≠ sK0 := superpose step161 step179
  subsumption step443 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1455_implies_Equation1632 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1455 G) : Equation1632 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ (Y ◇ (Y ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step14
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step27 step10
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step34
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step37 step10
  have step63 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step42 step11
  subsumption step63 step42


@[equational_result]
theorem Finite.Equation677_and_Equation151_implies_Equation203 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation151 G) : Equation203 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step16 step15
  have step20 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step19
  have step21 : sK0 ≠ (sK0 ◇ sK0) := superpose step19 step10
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step19 step12
  have step26 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step16 step24
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step16
  have step60 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step12 step46
  have step69 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step26 step12
  have step71 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step26 step69
  have step121 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose step71 step16
  have step125 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step121
  have step148 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step26 step18
  have step155 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step125 step148
  have step166 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step60 step155
  have step170 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step166 step26
  have step220 : sK0 ≠ sK0 := superpose step170 step21
  subsumption step220 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1525_implies_Equation1647 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1525 G) : Equation1647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ Y) ◇ (Y ◇ X)) ◇ ((Y ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ (((Y ◇ Y) ◇ X) ◇ ((Y ◇ Y) ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (Y ◇ (s ◇ s))) := by
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
  have step17 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = X1 := superpose step11 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step11 step11
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step29 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step14 step16
  have step38 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step13
  have step40 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ (X2 ◇ X0)) := superpose step13 step11
  have step124 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step38 step18
  have step177 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step124
  have step179 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step23 step177
  have step180 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step179
  have step186 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step180 step38
  have step188 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step180 step17
  have step199 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step188 step186
  have step309 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2))) = X2 := superpose step40 step17
  have step328 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2)) = X2 := superpose step199 step309
  have step380 (X1 X2 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X2)) = X2 := superpose step13 step328
  have step419 (X1 X2 : G) :  (X1 ◇ (X1 ◇ X2)) = X2 := superpose step199 step380
  have step750 : sK0 ≠ sK0 := superpose step419 step12
  subsumption step750 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation159_implies_Equation825 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation159 G) : Equation825 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step16 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step48 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose step20 step9
  have step64 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step12
  have step74 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step9 step64
  have step329 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step20
  have step366 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step329 step48
  have step395 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step74 step366
  have step400 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step395
  have step551 : sK0 ≠ sK0 := superpose step400 step15
  subsumption step551 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation160_implies_Equation258 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation160 G) : Equation258 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ (Y ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (s ◇ Y)) := by
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
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step14
  have step39 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step33 step13
  have step56 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step39 step12
  have step107 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step56 step11
  have step114 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step56 step12
  subsumption step107 step114


@[equational_result]
theorem Finite.Equation677_and_Equation1629_implies_Equation1832 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1629 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step16 step15
  have step27 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step20 step11
  have step28 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step17 step27
  have step29 : sK0 ≠ sK0 := superpose step28 step10
  subsumption step29 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1632_implies_Equation1658 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1632 G) : Equation1658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step17
  have step31 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose step23 step23
  have step72 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step31 step11
  have step76 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X2))) = X2 := superpose step31 step12
  have step93 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step16
  have step121 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step12
  have step128 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step76 step121
  have step131 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step93 step128
  have step153 (X0 X1 X2 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose step13 step31
  have step154 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose step131 step153
  have step171 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose step72 step154
  have step188 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step131 step171
  have step232 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := superpose step131 step10
  have step233 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step131 step232
  subsumption step233 step188


@[equational_result]
theorem Finite.Equation677_and_Equation1647_implies_Equation1682 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1647 G) : Equation1682 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step11 step9
  have step20 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step16 step20
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step16 step11
  have step31 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step16 step12
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step30 step25
  have step80 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose step50 step10
  subsumption step80 step31


@[equational_result]
theorem Finite.Equation677_and_Equation1648_implies_Equation1728 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1648 G) : Equation1728 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
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
  have step21 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step13
  have step22 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step12
  have step25 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step21
  have step26 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose step25 step11
  have step34 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step12 step14
  have step35 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step10 step14
  have step46 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step35 step34
  have step57 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step10 step46
  have step112 : sK0 ≠ sK0 := superpose step57 step26
  subsumption step112 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation55 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation55 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step27 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step51 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step27 step17
  have step52 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step51
  have step92 : sK0 ≠ sK0 := superpose step52 step13
  subsumption step92 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1657_implies_Equation1860 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1657 G) : Equation1860 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step79 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step92 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step79 step19
  have step102 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step92
  have step269 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step102 step12
  have step276 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step19 step269
  have step372 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step276 step22
  have step393 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step372
  have step438 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) ◇ X1)) = X1 := superpose step20 step17
  have step467 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X1)) = X1 := superpose step393 step438
  have step494 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose step11 step467
  have step575 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := superpose step393 step10
  subsumption step575 step494


@[equational_result]
theorem Finite.Equation677_and_Equation1658_implies_Equation1662 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1658 G) : Equation1662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step26 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step10 step13
  have step28 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step13 step10
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step26 step10
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step28 step45
  have step64 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step46 step10
  have step316 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step64 step11
  subsumption step316 step64


@[equational_result]
theorem Finite.Equation677_and_Equation1662_implies_Equation1838 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1662 G) : Equation1838 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step12 (X Y Z : G) : ((X ◇ ((Y ◇ Z) ◇ Z)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ ((Y ◇ Z) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ ((Y ◇ Z) ◇ Z))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X2 X3 : G) :  (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose step10 step10
  have step16 (X0 X1 X2 X3 : G) :  ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) = X1 := superpose step10 step10
  have step33 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step10 step14
  have step69 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step33 step15
  have step92 (X0 X1 X2 X3 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) := superpose step15 step14
  have step104 (X1 X2 X3 : G) :  ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) = X1 := superpose step14 step92
  have step160 (X0 X1 X2 X3 : G) :  (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) := superpose step104 step12
  have step175 (X0 X1 X2 : G) :  ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2))) = X1 := superpose step33 step16
  have step238 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose step160 step175
  have step242 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step69 step238
  have step269 : sK0 ≠ sK0 := superpose step242 step11
  subsumption step269 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation167_implies_Equation222 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation167 G) : Equation222 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step45 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step19 step12
  have step49 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step45
  have step53 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step9 step49
  have step130 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step53 step49
  have step131 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step49 step130
  have step181 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step131 step49
  have step1527 : sK0 ≠ sK0 := superpose step181 step10
  subsumption step1527 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1682_implies_Equation1722 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1682 G) : Equation1722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step52 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step14 step19
  have step77 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step52
  have step80 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step77 step12
  have step82 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step77 step12
  have step88 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step82 step80
  have step90 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step22 step88
  have step94 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step22 step9
  have step95 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step94
  have step107 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step95 step9
  have step136 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step14 step20
  have step149 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose step20 step19
  have step164 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step90 step136
  have step173 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step90 step164
  have step181 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step107 step19
  have step183 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step107 step20
  have step191 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step90 step183
  have step197 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step173 step191
  have step198 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step12 step197
  have step199 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step181 step198
  have step216 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step107 step15
  have step246 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step181 step216
  have step264 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step90 step246
  have step273 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step181 step264
  have step281 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step95 step273
  have step286 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step199 step281
  have step302 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step286 step9
  have step322 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step286 step10
  have step1412 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step286 step149
  have step1448 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) = (X0 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step149 step20
  have step1455 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step19 step1448
  have step1493 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step286 step1455
  have step1519 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step286 step1493
  have step1534 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1412 step1519
  have step1541 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1412 step1534
  have step1593 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step149 step302
  have step1667 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose step286 step1593
  have step1715 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose step1541 step1667
  have step1739 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step302 step1715
  have step1878 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step302 step1739
  have step2200 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step1878 step322
  subsumption step2200 step1739


@[equational_result]
theorem Finite.Equation677_and_Equation1691_implies_Equation3353 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1691 G) : Equation3353 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step9 step12
  have step59 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step19 step17
  have step74 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step59
  have step273 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step74 step10
  subsumption step273 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1722_implies_Equation1885 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1722 G) : Equation1885 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((((Y ◇ Y) ◇ X) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((s ◇ Y) ◇ Y)) := by
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
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose step13 step13
  have step38 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step13
  have step47 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step38 step16
  have step54 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step47
  have step78 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step54 step14
  have step80 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step54 step11
  have step87 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose step54 step12
  have step143 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step78 step15
  have step145 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step78 step11
  have step146 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step54 step145
  have step147 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step15 step143
  have step158 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step146 step147
  have step468 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose step19 step158
  have step477 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step80 step158
  have step515 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := superpose step54 step468
  have step529 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step477 step515
  have step1531 : sK0 ≠ sK0 := superpose step529 step87
  subsumption step1531 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1728_implies_Equation1841 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1728 G) : Equation1841 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ Y) ◇ X)) ◇ ((Y ◇ Y) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
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
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step10 step14
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step10 step14
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step12 step10
  have step39 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step30 step13
  have step41 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step21 step39
  have step59 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step41 step10
  have step78 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step59 step22
  have step86 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step41 step78
  have step152 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step86 step10
  have step153 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step86 step12
  have step154 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ X1) := superpose step86 step19
  have step166 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step86 step11
  have step180 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step86 step15
  have step233 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step86 step180
  have step1136 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step153
  have step1748 (X0 X1 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step34 step20
  have step1759 (X0 X1 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := superpose step154 step1748
  have step1819 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step86 step1759
  have step1867 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step86 step1819
  have step1898 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step153 step1867
  have step2909 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step233 step1136
  have step3028 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step1898 step2909
  have step3058 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step152 step3028
  have step3930 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step3058 step153
  have step3955 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step153 step3930
  have step4281 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step153 step3955
  have step4769 : sK0 ≠ sK0 := superpose step4281 step166
  subsumption step4769 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1832_implies_Equation2035 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1832 G) : Equation2035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step15 step12
  have step25 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step23
  have step35 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step15 step16
  have step36 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step16 step16
  have step37 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step16
  have step40 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step16 step12
  have step41 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step16 step11
  have step43 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step16 step12
  have step44 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) := superpose step16 step11
  have step45 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step18 step35
  have step48 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step25 step45
  have step113 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step25 step18
  have step127 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step113 step12
  have step128 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step113 step25
  have step135 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step113 step16
  have step136 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step113 step12
  have step138 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step16 step135
  have step140 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step127 step138
  have step145 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step48 step16
  have step150 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose step12 step145
  have step155 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step113 step150
  have step635 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step113 step40
  have step657 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step16 step635
  have step687 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step127 step657
  have step700 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step140 step687
  have step1486 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step16
  have step1490 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step140 step41
  have step1491 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step43
  have step1506 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step1491
  have step1507 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step140 step1490
  have step1511 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step1486
  have step1524 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step1506
  have step1525 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step155 step1507
  have step2869 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step700 step37
  have step2871 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step700 step41
  have step2897 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step12 step2871
  have step2899 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step12 step2869
  have step2913 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step1525 step2897
  have step2914 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step2899
  have step2922 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step2913 step2914
  have step2923 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step700 step2922
  have step3127 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step2923 step36
  have step3139 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step2923 step18
  have step3141 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step2923 step12
  have step3185 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step1524 step3141
  have step3186 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step127 step3139
  have step3197 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step1524 step3127
  have step3242 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step3186 step3197
  have step3272 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step140 step3242
  have step3289 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step1511 step3272
  have step3301 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step1524 step3289
  have step3307 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3185 step3301
  have step3311 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3186 step3307
  have step4000 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step3311 step12
  have step4006 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step3311 step37
  have step4010 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step3311 step44
  have step4039 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step1524 step4010
  have step4043 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3186 step4006
  have step4049 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step1524 step4000
  have step4066 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step3311 step4039
  have step4070 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step11 step4043
  have step4075 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3311 step4049
  have step4089 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step2913 step4066
  have step4092 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step136 step4070
  have step4096 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step3186 step4075
  have step4106 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3186 step4089
  have step4109 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step128 step4092
  have step4118 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step128 step4106
  have step4120 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step4109
  have step4971 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step4120 step10
  have step4972 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step4096 step4971
  subsumption step4972 step4118


@[equational_result]
theorem Finite.Equation677_and_Equation1838_implies_Equation1861 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1838 G) : Equation1861 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step11 step9
  have step27 : sK0 ≠ sK0 := superpose step17 step10
  subsumption step27 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1841_implies_Equation1924 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1841 G) : Equation1924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ (Y ◇ Y)) ◇ ((X ◇ (Y ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (s ◇ (s ◇ Y))) := by
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
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose step10 step13
  have step19 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step13 step10
  have step21 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step10 step14
  have step24 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step14
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step24 step13
  have step33 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose step12 step14
  have step34 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step12 step14
  have step37 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step27 step12
  have step41 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose step27 step12
  have step46 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step27 step19
  have step54 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step37 step46
  have step58 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step41 step54
  have step72 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step58 step12
  have step760 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step16 step21
  have step767 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose step34 step760
  have step794 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step10 step767
  have step812 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step58 step794
  have step828 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step58 step812
  have step859 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose step33 step72
  have step901 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step58 step859
  have step1186 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose step828 step72
  have step1189 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step901 step1186
  have step2473 : sK0 ≠ sK0 := superpose step1189 step11
  subsumption step2473 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1851_implies_Equation2254 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1851 G) : Equation2254 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ (Y ◇ Y)) ◇ (Y ◇ (X ◇ (Y ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (s ◇ (Y ◇ s))) := by
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
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step10 step13
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step10 step18
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step20 step23
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step20 step13
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step29
  have step39 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step31 step12
  have step53 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step26 step13
  have step56 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step53
  have step61 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step56
  have step64 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step39 step61
  have step65 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step64
  have step74 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step65 step10
  have step76 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose step65 step11
  have step633 : sK0 ≠ sK0 := superpose step74 step76
  subsumption step633 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1860_implies_Equation2043 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1860 G) : Equation2043 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step13 step12
  have step27 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step24
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step27 step12
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step35
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step38 step19
  have step82 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step63
  have step97 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step82 step12
  have step102 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step97
  have step106 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step38 step102
  have step188 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose step106 step9
  have step205 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := superpose step106 step10
  have step570 : sK0 ≠ sK0 := superpose step188 step205
  subsumption step570 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1861_implies_Equation2044 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1861 G) : Equation2044 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step18 step9
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step25 step11
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step30
  have step52 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step34 step25
  have step61 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step34 step17
  have step91 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step52 step61
  have step95 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step52 step91
  have step98 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step34 step95
  have step102 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step98 step9
  have step113 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step98 step10
  have step114 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step98 step113
  subsumption step114 step102


@[equational_result]
theorem Finite.Equation677_and_Equation1885_implies_Equation1898 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1885 G) : Equation1898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step9
  have step17 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step12
  have step42 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step24 step12
  have step45 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step42
  have step47 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step20 step17
  have step58 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step45 step47
  have step68 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step58 step12
  have step72 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step68
  have step89 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step18 step12
  have step94 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step72 step89
  have step100 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step94
  have step122 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step72 step10
  have step671 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step19 step100
  have step701 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step100 step671
  have step718 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step100 step701
  have step946 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step718 step100
  have step1734 : sK0 ≠ sK0 := superpose step946 step122
  subsumption step1734 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1895_implies_Equation2091 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1895 G) : Equation2091 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ X) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ s)) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step12
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step14
  have step41 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step32 step12
  have step42 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step41
  have step80 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step42 step11
  subsumption step80 step12


@[equational_result]
theorem Finite.Equation677_and_Equation1898_implies_Equation1921 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1898 G) : Equation1921 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ (Y ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => (Y ◇ (s ◇ Y))) := by
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
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose step11 step11
  have step22 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose step11 step15
  have step26 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step13
  have step28 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step11 step16
  have step30 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step37 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step32
  have step42 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step37 step11
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step37 step14
  have step44 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step43
  have step45 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step42
  have step115 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose step45 step26
  have step117 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step45 step14
  have step118 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step45 step13
  have step119 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step45 step11
  have step131 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step26 step17
  have step137 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step45 step17
  have step172 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step45 step137
  have step178 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) := superpose step44 step131
  have step201 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose step45 step178
  have step214 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step172 step201
  have step222 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step45 step214
  have step235 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0))) := superpose step14 step28
  have step238 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step15 step28
  have step255 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step115 step238
  have step258 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = ((X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) := superpose step115 step235
  have step273 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose step172 step255
  have step276 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step45 step258
  have step289 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step172 step273
  have step292 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step45 step276
  have step300 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step222 step289
  have step308 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step45 step300
  have step311 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X1) := superpose step292 step308
  have step522 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step117 step15
  have step532 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step115 step522
  have step591 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose step22 step117
  have step592 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step311 step591
  have step619 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step45 step592
  have step643 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step117 step619
  have step721 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) := superpose step30 step118
  have step743 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) := superpose step115 step721
  have step765 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose step532 step743
  have step985 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X1 := superpose step14 step119
  have step1031 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X1 := superpose step172 step985
  have step1054 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) = X1 := superpose step643 step1031
  have step1071 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := superpose step45 step1054
  have step1080 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step765 step1071
  have step1394 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step1080 step12
  subsumption step1394 step1080


@[equational_result]
theorem Finite.Equation677_and_Equation1921_implies_Equation2054 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1921 G) : Equation2054 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step9 step12
  have step22 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step12
  have step27 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step9
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step27
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step28 step12
  have step55 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step37 step22
  have step57 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step55
  have step118 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step57 step9
  have step127 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose step57 step10
  have step174 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step19 step12
  have step179 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step12 step174
  have step194 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step118 step179
  have step220 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step194 step194
  have step259 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step9 step220
  have step402 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step259 step12
  have step866 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step259 step402
  have step1914 : sK0 ≠ sK0 := superpose step866 step127
  subsumption step1914 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1924_implies_Equation2247 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1924 G) : Equation2247 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ s)) (fun s => (Y ◇ s)) := by
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
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step12 step12
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step10 step12
  have step21 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step13
  have step29 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step21 step11
  have step40 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step10
  have step180 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step40
  have step181 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step40
  have step213 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step10 step181
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step12 step180
  have step215 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step213 step214
  have step536 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step215 step14
  have step549 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step536
  have step672 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step10 step549
  have step827 : sK0 ≠ sK0 := superpose step672 step29
  subsumption step827 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation203_implies_Equation307 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation203 G) : Equation307 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step11
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step18
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step21
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step19 step11
  have step28 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step23 step19
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step28
  have step41 : sK0 ≠ (sK0 ◇ sK0) := superpose step35 step10
  subsumption step41 step35


@[equational_result]
theorem Finite.Equation677_and_Equation2035_implies_Equation2238 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2035 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step15 step9
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step21 step12
  have step34 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step17 step32
  have step42 : sK0 ≠ sK0 := superpose step34 step10
  subsumption step42 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2043_implies_Equation2669 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2043 G) : Equation2669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose step12 step9
  have step26 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step17 step9
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step9
  have step33 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step23 step12
  have step34 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step23 step11
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step30 step34
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step30 step33
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step39
  have step44 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step26 step40
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step30 step43
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step44 step45
  have step50 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step46 step9
  have step281 : sK0 ≠ (sK0 ◇ sK0) := superpose step50 step10
  subsumption step281 step46


@[equational_result]
theorem Finite.Equation677_and_Equation2044_implies_Equation2060 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2044 G) : Equation2060 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step15
  have step32 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose step21 step11
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step11
  have step37 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step33 step32
  have step40 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step33 step37
  have step75 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := superpose step33 step12
  have step76 : sK0 ≠ (sK0 ◇ sK0) := superpose step40 step75
  subsumption step76 step33


@[equational_result]
theorem Finite.Equation677_and_Equation2054_implies_Equation2061 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2054 G) : Equation2061 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ (Y ◇ Y)) ◇ Y) ◇ (X ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => ((s ◇ Y) ◇ s)) := by
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
  have step16 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step10 step10
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step13
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step21 step16
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step10
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step16 step26
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step27
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step38 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step14 step10
  have step39 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step29 step38
  have step52 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step29 step10
  have step67 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step12 step13
  have step74 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step29 step67
  have step99 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0))) := superpose step14 step74
  have step133 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step52 step99
  have step178 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step39 step14
  have step184 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose step33 step178
  have step202 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step133 step184
  have step209 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := superpose step133 step202
  have step239 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose step209 step11
  subsumption step239 step74


@[equational_result]
theorem Finite.Equation677_and_Equation2060_implies_Equation2449 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2060 G) : Equation2449 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X1)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step12
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step11
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose step17 step18
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step11 step18
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step26 step31
  have step53 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step37 step12
  have step57 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step48 step53
  have step59 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step37 step57
  have step88 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose step59 step9
  have step145 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step19
  have step161 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step19 step12
  have step166 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step12 step161
  have step179 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose step37 step145
  have step182 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step88 step166
  have step193 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose step59 step179
  have step204 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := superpose step182 step193
  have step209 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step9 step204
  have step239 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step209 step10
  subsumption step239 step209


@[equational_result]
theorem Finite.Equation677_and_Equation2061_implies_Equation2101 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2061 G) : Equation2101 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ X) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ s)) (fun s => (s ◇ Y)) := by
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
  have step22 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step10 step13
  have step36 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step12 step14
  have step51 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step10 step36
  have step54 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step22 step51
  have step58 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step51 step13
  have step88 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step58 step12
  have step165 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step88 step11
  have step179 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step54 step165
  subsumption step179 step51


@[equational_result]
theorem Finite.Equation677_and_Equation2064_implies_Equation3059 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2064 G) : Equation3059 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step13 (X Y : G) : (((X ◇ Y) ◇ (Y ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose step13 step13
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step15
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step29 step13
  have step52 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose step29 step11
  have step53 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose step19 step52
  have step58 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := superpose step44 step53
  have step95 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := superpose step44 step12
  subsumption step95 step58


@[equational_result]
theorem Finite.Equation677_and_Equation206_implies_Equation639 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation206 G) : Equation639 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (s ◇ Y))) := by
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
  have step21 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step10 step13
  have step22 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step10
  have step25 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step21
  have step33 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step10 step14
  have step34 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step12 step14
  have step45 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step34 step33
  have step56 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step12 step45
  have step82 : sK0 ≠ (sK0 ◇ sK0) := superpose step56 step11
  subsumption step82 step25


@[equational_result]
theorem Finite.Equation677_and_Equation2088_implies_Equation3069 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2088 G) : Equation3069 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step194 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X1))) := superpose step13 step21
  have step238 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step12 step194
  have step1120 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step19 step21
  have step1125 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step12 step1120
  have step1148 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step238 step1125
  have step1210 : sK0 ≠ sK0 := superpose step1148 step10
  subsumption step1210 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation209_implies_Equation1026 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation209 G) : Equation1026 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 : sK0 ≠ (sK0 ◇ sK0) := superpose step10 step11
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step10 step14
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step30 step13
  have step56 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step10
  have step99 : sK0 ≠ sK0 := superpose step56 step16
  subsumption step99 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2091_implies_Equation2697 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2091 G) : Equation2697 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ (X ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => ((Y ◇ s) ◇ s)) := by
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
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step10 step13
  have step33 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step12 step12
  have step37 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step19 step33
  have step41 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step37 step14
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step41
  have step70 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step46 step10
  have step76 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step46 step11
  have step678 : sK0 ≠ sK0 := superpose step70 step76
  subsumption step678 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2101_implies_Equation2125 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2101 G) : Equation2125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Y))) (fun s => ((Y ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step29 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step14 step15
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step13 step15
  have step32 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step11
  have step33 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step32 step30
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step15
  have step97 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose step46 step12
  have step132 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step46 step29
  have step237 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose step46 step32
  have step254 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step32 step11
  have step289 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step46 step254
  have step302 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step132 step237
  have step325 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step132 step289
  have step353 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step302 step325
  have step377 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step46 step353
  have step662 : sK0 ≠ sK0 := superpose step377 step97
  subsumption step662 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2125_implies_Equation2263 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2125 G) : Equation2263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step17 step9
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step17 step22
  have step39 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step27 step32
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step17 step39
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step39 step12
  have step52 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step45
  have step53 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := superpose step17 step20
  have step55 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0)) := superpose step11 step20
  have step75 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) := superpose step12 step55
  have step77 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step52 step53
  have step83 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := superpose step52 step75
  have step90 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step52 step9
  have step351 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose step11 step90
  have step400 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step83 step351
  have step592 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step400 step12
  have step601 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step77 step592
  have step835 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step601 step10
  subsumption step835 step43


@[equational_result]
theorem Finite.Equation677_and_Equation222_implies_Equation228 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation222 G) : Equation228 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step11 step11
  have step26 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step13 step15
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step15
  have step40 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step15 step26
  have step44 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step17 step40
  have step101 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step14 step44
  have step130 : sK0 ≠ (sK0 ◇ sK0) := superpose step101 step12
  subsumption step130 step30


@[equational_result]
theorem Finite.Equation677_and_Equation2238_implies_Equation2441 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2238 G) : Equation2441 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step9 step12
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step16
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step12
  have step27 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step21 step12
  have step28 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step21 step12
  have step30 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step28 step27
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step18 step30
  have step33 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step19
  have step57 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step17
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step33 step17
  have step80 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step12 step63
  have step84 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step57
  have step86 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step80 step84
  have step88 : sK0 ≠ (sK0 ◇ sK0) := superpose step86 step10
  have step89 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step86 step11
  subsumption step88 step89


@[equational_result]
theorem Finite.Equation677_and_Equation2247_implies_Equation2444 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2247 G) : Equation2444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((X ◇ Y) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (s ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step28 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step10 step14
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step28 step12
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step36
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step38 step12
  have step65 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step44 step11
  have step71 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step44 step10
  subsumption step65 step71


@[equational_result]
theorem Finite.Equation677_and_Equation2254_implies_Equation2467 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2254 G) : Equation2467 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (Y ◇ ((X ◇ Y) ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (s ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (Y ◇ (s ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step10 step14
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step14
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step22 step12
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step32
  have step39 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step36 step12
  have step42 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step39
  have step83 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step42 step10
  have step91 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose step42 step11
  have step341 : sK0 ≠ sK0 := superpose step83 step91
  subsumption step341 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2263_implies_Equation2304 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2263 G) : Equation2304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step13
  have step20 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step9 step11
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step11
  have step29 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step12
  have step30 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step14 step12
  have step31 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step39 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step31 step30
  have step40 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step29
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step39
  have step47 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step41 step10
  have step61 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step40 step12
  have step62 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step40 step9
  have step69 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step9 step62
  have step70 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose step41 step61
  have step80 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose step69 step70
  have step85 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step9 step80
  have step96 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose step20 step20
  have step103 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose step20 step11
  have step106 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step41 step103
  have step110 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X1 := superpose step85 step96
  have step114 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step20 step106
  have step116 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose step20 step110
  have step118 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose step114 step116
  have step119 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step41 step118
  have step122 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step119
  have step145 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step119 step122
  have step865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step145 step145
  have step4328 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step865 step47
  have step4403 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step145 step4328
  subsumption step4403 step119


@[equational_result]
theorem Finite.Equation677_and_Equation228_implies_Equation261 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation228 G) : Equation261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step29 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step9 step12
  have step39 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step9 step29
  have step48 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step39 step39
  have step58 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose step9 step48
  have step67 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step9 step58
  have step85 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step67 step12
  have step275 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step67 step85
  have step732 : sK0 ≠ sK0 := superpose step275 step10
  subsumption step732 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2304_implies_Equation2327 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2304 G) : Equation2327 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) := by
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
  have step28 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step11 step15
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step14 step15
  have step32 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step13
  have step33 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step32 step30
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step15
  have step86 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step46 step14
  have step95 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose step46 step12
  have step130 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step46 step28
  have step176 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step13 step86
  have step185 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose step86 step16
  have step190 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step130 step185
  have step196 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step46 step176
  have step237 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step32 step13
  have step241 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1))) := superpose step32 step86
  have step254 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step46 step241
  have step258 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step46 step237
  have step293 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step130 step254
  have step297 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step190 step258
  have step322 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step196 step293
  have step325 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step130 step297
  have step349 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step46 step325
  have step379 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := superpose step11 step349
  have step466 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step46 step379
  have step494 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step322 step466
  have step705 : sK0 ≠ (sK0 ◇ sK0) := superpose step494 step95
  subsumption step705 step46


@[equational_result]
theorem Finite.Equation677_and_Equation2327_implies_Equation2497 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2327 G) : Equation2497 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step13
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step11
  have step27 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step12
  have step28 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step14 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step36 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step29 step28
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := superpose step9 step27
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step36
  have step45 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step38 step10
  have step76 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose step37 step29
  have step91 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose step12 step76
  have step96 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose step14 step91
  have step99 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step38 step96
  have step118 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step99 step29
  have step121 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step99 step12
  have step124 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step121 step118
  have step1005 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step124 step124
  have step5966 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step1005 step45
  have step6035 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step124 step5966
  subsumption step6035 step99


@[equational_result]
theorem Finite.Equation677_and_Equation2337_implies_Equation3281 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2337 G) : Equation3281 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose step9 step13
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step14
  have step32 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step12
  have step42 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step32
  have step56 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step42 step12
  have step57 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step42 step9
  have step64 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step15 step57
  have step65 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose step15 step56
  have step75 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose step64 step65
  have step85 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step9 step75
  have step102 : sK0 ≠ (sK0 ◇ sK0) := superpose step85 step10
  subsumption step102 step15


@[equational_result]
theorem Finite.Equation677_and_Equation23_implies_Equation47 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation23 G) : Equation47 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step17 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step18 step17
  have step23 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step15 step22
  have step24 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step23 step10
  subsumption step24 step15


@[equational_result]
theorem Finite.Equation677_and_Equation2441_implies_Equation2644 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2441 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose step9 step11
  have step16 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step11 step13
  have step17 (X0 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step9 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step16 step19
  have step22 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step9 step17
  have step23 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step22
  have step25 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step23 step10
  subsumption step25 step21


@[equational_result]
theorem Finite.Equation677_and_Equation2444_implies_Equation2530 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2444 G) : Equation2530 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (((X ◇ Y) ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((s ◇ s) ◇ Y))) := by
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
  have step15 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) = X1 := superpose step10 step13
  have step20 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X1 := superpose step10 step14
  have step26 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1))) := superpose step12 step12
  have step164 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := superpose step26 step14
  have step170 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step14 step164
  have step222 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step13 step15
  have step244 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step222 step14
  have step256 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step244
  have step407 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step256 step170
  have step411 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step256 step407
  have step971 : sK0 ≠ (sK0 ◇ sK0) := superpose step411 step11
  subsumption step971 step256


@[equational_result]
theorem Finite.Equation677_and_Equation2449_implies_Equation2653 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2449 G) : Equation2653 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step9 step18
  have step24 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)))) := superpose step9 step23
  have step28 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step23
  have step35 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) := superpose step28 step24
  have step38 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose step9 step35
  have step40 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose step9 step38
  have step41 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step9 step40
  have step63 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step28 step10
  have step64 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step28 step63
  have step164 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step41 step12
  have step171 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step41 step164
  have step279 : sK0 ≠ sK0 := superpose step171 step64
  subsumption step279 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2460_implies_Equation3113 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2460 G) : Equation3113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((Y ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step24 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step12 step13
  have step53 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := superpose step24 step11
  subsumption step53 step10


@[equational_result]
theorem Finite.Equation677_and_Equation2467_implies_Equation2650 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2467 G) : Equation2650 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((Y ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step12 step14
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step14 step12
  have step36 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step12 step28
  have step49 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step12 step36
  have step59 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step49 step14
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step14 step59
  have step86 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step63 step14
  have step89 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step24 step86
  have step94 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step63 step89
  have step99 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose step12 step24
  have step141 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose step94 step99
  have step153 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step94 step141
  have step159 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step14 step153
  have step185 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose step94 step11
  subsumption step185 step159


@[equational_result]
theorem Finite.Equation677_and_Equation2497_implies_Equation2506 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2497 G) : Equation2506 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := mod_symm nh
  have step16 (X Y : G) : (Y ◇ (((X ◇ Y) ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ ((s ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step18
  have step47 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step31 step16
  have step83 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step47 step16
  have step85 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step47 step83
  have step142 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step85 step16
  have step1880 : sK0 ≠ (sK0 ◇ sK0) := superpose step142 step13
  subsumption step1880 step85


@[equational_result]
theorem Finite.Equation677_and_Equation2506_implies_Equation2540 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2506 G) : Equation2540 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step9 step18
  have step24 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step23
  have step28 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step23
  have step35 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step28 step24
  have step36 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose step28 step35
  have step37 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose step9 step36
  have step38 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step9 step37
  have step68 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose step28 step10
  have step149 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step38 step12
  have step294 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step149 step12
  have step481 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step294 step11
  have step487 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step294 step38
  have step495 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step11 step481
  have step520 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step487 step495
  have step766 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step38 step520
  have step1086 : sK0 ≠ (sK0 ◇ sK0) := superpose step766 step68
  subsumption step1086 step28


@[equational_result]
theorem Finite.Equation677_and_Equation2507_implies_Equation3116 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2507 G) : Equation3116 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step15 (X Y : G) : ((((Y ◇ X) ◇ Y) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => ((s ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step13 step15


@[equational_result]
theorem Finite.Equation677_and_Equation2530_implies_Equation2647 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2530 G) : Equation2647 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step9 step18
  have step28 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step23
  have step32 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step23 step9
  have step33 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step23 step32
  have step36 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step28 step33
  have step39 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose step23 step36
  have step80 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step28 step10
  have step168 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose step39 step39
  have step187 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step14 step168
  have step282 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step187 step12
  have step431 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step282 step12
  have step440 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose step282 step19
  have step669 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step431 step431
  have step678 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step282 step431
  have step886 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step669 step187
  have step2821 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step886 step440
  have step2830 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step669 step2821
  have step2871 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step678 step2830
  have step8808 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step2871 step431
  have step8831 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step431 step8808
  have step9608 : sK0 ≠ sK0 := superpose step8831 step80
  subsumption step9608 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2534_implies_Equation1113 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2534 G) : Equation1113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (s ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (s ◇ Y)) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step11 step12


@[equational_result]
theorem Finite.Equation677_and_Equation2538_implies_Equation1117 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2538 G) : Equation1117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have step12 (X Y Z : G) : (Y ◇ ((Y ◇ (X ◇ Z)) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (s ◇ Z)) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (s ◇ Z)) ◇ Z)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step11 step12


@[equational_result]
theorem Finite.Equation677_and_Equation2540_implies_Equation2660 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2540 G) : Equation2660 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step11 step9
  have step18 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step17
  have step19 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := superpose step9 step19
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step18 step12
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step25
  have step54 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose step35 step10
  have step108 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X0)) := superpose step25 step20
  have step125 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step108
  have step132 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step26 step125
  have step136 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step35 step132
  have step160 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step136 step12
  have step732 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step136 step160
  have step1280 : sK0 ≠ sK0 := superpose step732 step54
  subsumption step1280 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation258_implies_Equation263 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation258 G) : Equation263 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((X ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step11 step11
  have step34 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose step13 step17
  have step51 : sK0 ≠ sK0 := superpose step34 step12
  subsumption step51 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation102 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation102 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step12
  have step32 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step24 step9
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step32
  have step64 : sK0 ≠ sK0 := superpose step33 step13
  subsumption step64 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation261_implies_Equation274 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation261 G) : Equation274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ Y) ◇ s)) := by
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
  have step22 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step12 step13
  have step36 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step10 step14
  have step51 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step12 step36
  have step54 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step22 step51
  have step284 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step54 step11
  subsumption step284 step51


@[equational_result]
theorem Finite.Equation677_and_Equation263_implies_Equation362 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation263 G) : Equation362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step9
  have step23 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step14 step12
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step26
  have step35 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step23
  have step46 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step35
  have step67 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose step33 step46
  have step73 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose step9 step67
  have step74 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step9 step73
  have step156 : sK0 ≠ (sK0 ◇ sK0) := superpose step74 step10
  subsumption step156 step33


@[equational_result]
theorem Finite.Equation677_and_Equation2644_implies_Equation2847 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2644 G) : Equation2847 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step15
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step19 step12
  have step21 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step20
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step23
  have step30 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step24 step9
  have step34 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step24 step12
  have step36 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step34
  have step61 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := superpose step36 step10
  subsumption step61 step30


@[equational_result]
theorem Finite.Equation677_and_Equation2647_implies_Equation2855 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2647 G) : Equation2855 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ (X ◇ Y)) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ s) ◇ (s ◇ Y))) := by
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
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step10 step13
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step18
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step14
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step12
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step21 step34
  have step42 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step39 step12
  have step47 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step42
  have step66 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step47 step10
  have step248 : sK0 ≠ (sK0 ◇ sK0) := superpose step66 step11
  subsumption step248 step47


@[equational_result]
theorem Finite.Equation677_and_Equation2650_implies_Equation2865 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2650 G) : Equation2865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ s) ◇ (Y ◇ s))) := by
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
  have step23 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step10 step14
  have step29 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step23 step10
  have step73 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step29 step12
  have step88 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step73
  have step163 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step88 step10
  have step247 : sK0 ≠ (sK0 ◇ sK0) := superpose step163 step11
  subsumption step247 step88


@[equational_result]
theorem Finite.Equation677_and_Equation2653_implies_Equation2672 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2653 G) : Equation2672 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((X ◇ (Y ◇ Y)) ◇ Y) ◇ ((X ◇ (Y ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((X ◇ Y) ◇ (X ◇ Y)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ s) ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step11 step16
  have step34 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step31
  have step41 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step13 step14
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose step34 step41
  have step51 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step34 step44
  have step56 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step34 step51
  have step69 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := superpose step34 step12
  have step70 : sK0 ≠ (sK0 ◇ sK0) := superpose step56 step69
  subsumption step70 step34


@[equational_result]
theorem Finite.Equation677_and_Equation2660_implies_Equation2699 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2660 G) : Equation2699 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ Y) ◇ (s ◇ s))) := by
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
  have step18 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step13 step10
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step27 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) = X1 := superpose step13 step12
  have step50 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step27
  have step54 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step27 step12
  have step73 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step50 step27
  have step82 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step54 step73
  have step84 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step82
  have step152 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step84 step12
  have step191 (X0 X1 : G) :  ((X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1))) = X1 := superpose step20 step18
  have step209 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1))) = X1 := superpose step84 step191
  have step236 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = X1 := superpose step14 step209
  have step254 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step152 step236
  have step494 : sK0 ≠ (sK0 ◇ sK0) := superpose step254 step11
  subsumption step494 step84


@[equational_result]
theorem Finite.Equation677_and_Equation2669_implies_Equation3667 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2669 G) : Equation3667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step19
  have step26 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) := superpose step9 step25
  have step29 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0)))) = X0 := superpose step25 step25
  have step30 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0))) = X0 := superpose step9 step25
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step30 step29
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) := superpose step15 step26
  have step44 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step9 step42
  have step206 : sK0 ≠ (sK0 ◇ sK0) := superpose step44 step10
  subsumption step206 step41


@[equational_result]
theorem Finite.Equation677_and_Equation2672_implies_Equation2850 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2672 G) : Equation2850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step19
  have step27 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) = X1 := superpose step11 step24
  have step31 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step24 step12
  have step55 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X0)) := superpose step31 step12
  have step58 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step55
  have step97 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X2) ◇ (X2 ◇ X2)) := superpose step58 step58
  have step118 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose step58 step20
  have step120 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose step9 step118
  have step125 (X0 X1 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X0 := superpose step24 step120
  have step1049 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step125 step12
  have step1082 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step1049
  have step1232 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))))) ◇ (X0 ◇ (X2 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))))))) := superpose step27 step97
  have step1235 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0)))))) := superpose step1082 step1232
  have step1290 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose step27 step1235
  have step1334 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step1082 step1290
  have step1457 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step1082 step10
  have step1560 : sK0 ≠ (sK0 ◇ sK0) := superpose step1334 step1457
  subsumption step1560 step1082


@[equational_result]
theorem Finite.Equation677_and_Equation2697_implies_Equation2853 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2697 G) : Equation2853 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ ((X ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ (s ◇ s))) := by
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
  have step17 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := superpose step10 step13
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose step10 step14
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step27 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose step13 step12
  have step184 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step13 step17
  have step200 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step184 step12
  have step215 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step200
  have step273 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step215 step27
  have step274 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step215 step13
  have step294 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step215 step273
  have step306 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X1 ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose step27 step20
  have step356 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step274 step306
  have step373 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step294 step356
  have step386 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose step294 step12
  have step400 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step294 step10
  have step1305 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step21 step386
  have step1313 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X0) := superpose step27 step386
  have step1375 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step294 step1313
  have step1382 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose step373 step1305
  have step1395 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step1375 step1382
  have step1398 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step386 step1395
  have step1611 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step1398 step11
  subsumption step1611 step400


@[equational_result]
theorem Finite.Equation677_and_Equation2699_implies_Equation2710 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2699 G) : Equation2710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ X0) = X0 := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := superpose step9 step19
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step13
  have step86 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step50 step10
  have step215 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ X0)) := superpose step25 step20
  have step249 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step215
  have step256 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose step50 step249
  have step261 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step50 step256
  have step297 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step261 step12
  have step301 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step261 step20
  have step311 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step301
  have step467 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step311 step311
  have step469 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step20 step311
  have step475 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step311 step20
  have step506 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step297 step469
  have step508 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step475 step467
  have step520 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step311 step506
  have step1167 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step508 step86
  subsumption step1167 step520


@[equational_result]
theorem Finite.Equation677_and_Equation2710_implies_Equation2737 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2710 G) : Equation2737 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step14 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ (Y ◇ Y))) := by
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
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step37 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step14 step32
  have step41 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step37 step14
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step41
  have step111 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step46 step14
  have step121 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step46 step12
  have step532 : sK0 ≠ sK0 := superpose step111 step121
  subsumption step532 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation335 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation335 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step410 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step301 step11
  subsumption step410 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2737_implies_Equation2743 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2737 G) : Equation2743 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((((Y ◇ Y) ◇ X) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) := by
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
  have step38 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step11
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step38 step16
  have step53 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step48
  have step76 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := superpose step53 step12
  have step81 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step53 step14
  have step82 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step53 step13
  have step128 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step13 step81
  have step156 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step53 step128
  have step227 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step82 step15
  have step232 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step15 step227
  have step249 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step156 step232
  have step472 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step81 step249
  have step842 : sK0 ≠ (sK0 ◇ sK0) := superpose step472 step76
  subsumption step842 step53


@[equational_result]
theorem Finite.Equation677_and_Equation274_implies_Equation315 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation274 G) : Equation315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step13 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step11 step13
  have step24 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step11 step15
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step13 step15
  have step39 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step15 step24
  have step43 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step18 step39
  have step99 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step13 step43
  have step128 : sK0 ≠ (sK0 ◇ sK0) := superpose step99 step12
  subsumption step128 step29


@[equational_result]
theorem Finite.Equation677_and_Equation2743_implies_Equation2873 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2743 G) : Equation2873 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step19
  have step31 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step24 step12
  have step53 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step31 step12
  have step56 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step53
  have step74 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step56 step9
  have step75 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X1 := superpose step56 step9
  have step142 (X0 : G) :  (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step74 step9
  have step148 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step74 step56
  have step149 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step75 step148
  have step154 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step75 step142
  have step262 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose step154 step56
  have step277 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose step154 step10
  have step289 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step149 step262
  have step925 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step289 step12
  have step1563 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step289 step925
  have step2818 : sK0 ≠ sK0 := superpose step1563 step277
  subsumption step2818 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation280_implies_Equation622 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation280 G) : Equation622 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step9 step19
  have step41 : sK0 ≠ sK0 := superpose step24 step10
  subsumption step41 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2847_implies_Equation3050 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2847 G) : Equation3050 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step9 step15
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step12
  have step21 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step12
  have step23 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step20
  have step24 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step17 step23
  have step29 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step24 step9
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step24 step12
  have step55 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step29 step12
  have step57 : sK0 ≠ (sK0 ◇ sK0) := superpose step29 step10
  have step59 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step16 step55
  have step61 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step30 step59
  have step131 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step61 step19
  have step141 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step61 step131
  have step214 : sK0 ≠ sK0 := superpose step141 step57
  subsumption step214 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2850_implies_Equation2875 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2850 G) : Equation2875 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((X ◇ Y) ◇ Y) ◇ (((X ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (s ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((X ◇ Y) ◇ ((X ◇ Y) ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (s ◇ s)) ◇ Y)) := by
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
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step16 step11
  have step28 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step14 step14
  have step29 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step15 step14
  have step36 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose step13 step11
  have step72 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step36 step15
  have step113 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose step72 step36
  have step114 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1))) = X0 := superpose step72 step11
  have step115 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step72 step114
  have step116 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step72 step113
  have step129 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step25 step29
  have step156 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step115 step129
  have step170 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose step116 step156
  have step178 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose step28 step170
  have step182 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step14 step178
  have step183 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step115 step182
  have step198 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := superpose step183 step12
  have step199 : sK0 ≠ (sK0 ◇ sK0) := superpose step116 step198
  subsumption step199 step183


@[equational_result]
theorem Finite.Equation677_and_Equation2853_implies_Equation2900 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2853 G) : Equation2900 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ ((X ◇ Y) ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (s ◇ Y)) ◇ s)) := by
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
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step10
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step18 step10
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step18 step14
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step27
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step26 step30
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step18 step12
  have step38 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step14
  have step49 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step33 step14
  have step53 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step31 step49
  have step55 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step53
  have step81 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step55 step11
  subsumption step81 step38


@[equational_result]
theorem Finite.Equation677_and_Equation2855_implies_Equation3481 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2855 G) : Equation3481 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose step9 step19
  have step26 (X0 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step17 step12
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step17 step26
  have step32 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step31
  have step34 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step12 step24
  have step40 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X0)) := superpose step24 step12
  have step41 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) = X0 := superpose step24 step9
  have step48 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) := superpose step32 step40
  have step57 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step41 step48
  have step83 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0)) := superpose step12 step18
  have step91 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) ◇ X0))) := superpose step18 step24
  have step98 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step18 step91
  have step106 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step32 step98
  have step112 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) := superpose step18 step106
  have step116 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step18 step112
  have step123 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step57 step57
  have step368 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step57 step20
  have step470 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step116 step20
  have step476 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step11 step470
  have step745 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step16 step57
  have step748 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step476 step745
  have step791 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose step11 step748
  have step889 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step57 step791
  have step908 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step791 step12
  have step1128 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose step123 step123
  have step1151 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step123 step20
  have step1155 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose step123 step57
  have step1158 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step368 step1155
  have step1162 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step908 step1151
  have step1180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose step908 step1128
  have step1193 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step12 step1162
  have step1203 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step12 step1180
  have step1214 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step57 step1193
  have step1219 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step908 step1203
  have step1231 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step908 step1219
  have step1278 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step22 step20
  have step1291 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step12 step1278
  have step1324 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step1158 step1291
  have step1539 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose step1214 step1324
  have step1561 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X0 ◇ X1)) = X1 := superpose step1324 step57
  have step1608 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step889 step1561
  have step1626 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose step57 step1539
  have step1712 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose step57 step1608
  have step1719 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step1608
  have step1723 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step16 step1608
  have step1748 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step1608 step1324
  have step1749 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step57 step1748
  have step1767 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step1723
  have step1782 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := superpose step908 step1749
  have step1789 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose step1231 step1767
  have step1793 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose step1719 step1782
  have step1795 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step1719 step1789
  have step2096 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose step20 step1712
  have step2097 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step1324 step1712
  have step2144 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step1719 step2096
  have step2629 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step1626 step20
  have step2651 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step1719 step2629
  have step2893 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step57 step2097
  have step3648 (X0 X1 : G) :  ((X1 ◇ ((((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose step1626 step83
  have step3754 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose step2651 step3648
  have step3818 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step1795 step3754
  have step4025 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := superpose step2893 step2144
  have step4026 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step1793 step4025
  have step4115 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step1712 step4026
  have step4247 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))))) = X0 := superpose step116 step34
  have step4421 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := superpose step908 step4247
  have step4503 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step1719 step4421
  have step4566 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step11 step4503
  have step4740 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose step3818 step2893
  have step4743 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step4115 step4740
  have step4815 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step4566 step4743
  have step5292 : sK0 ≠ (sK0 ◇ sK0) := superpose step4815 step10
  subsumption step5292 step32


@[equational_result]
theorem Finite.Equation677_and_Equation2865_implies_Equation3868 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2865 G) : Equation3868 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X0 := superpose step9 step9
  have step36 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step13
  have step54 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X0 := superpose step36 step13
  have step109 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) := superpose step54 step11
  have step120 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ X0) := superpose step9 step109
  have step132 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step36 step120
  have step209 : sK0 ≠ (sK0 ◇ sK0) := superpose step132 step10
  subsumption step209 step36


@[equational_result]
theorem Finite.Equation677_and_Equation2873_implies_Equation2903 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2873 G) : Equation2903 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ (Y ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (Y ◇ Y)) ◇ s)) := by
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
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose step12 step12
  have step21 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step12 step13
  have step40 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step21 step14
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step21 step40
  have step46 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step44 step21
  have step47 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step44 step12
  have step56 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step44 step11
  have step100 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) := superpose step21 step19
  have step135 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step46 step100
  have step153 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step44 step135
  have step163 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step44 step153
  have step167 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step47 step163
  have step171 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step167
  have step199 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step44 step171
  have step1482 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step199 step56
  subsumption step1482 step167


@[equational_result]
theorem Finite.Equation677_and_Equation2875_implies_Equation3053 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2875 G) : Equation3053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := superpose step9 step17
  have step25 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step12
  have step38 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ X0)) := superpose step25 step12
  have step40 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step38
  have step65 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step40 step12
  have step68 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step40 step9
  have step97 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step68 step12
  have step102 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step18 step97
  have step104 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step65 step102
  have step135 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step104 step21
  have step136 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step104 step9
  have step142 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step104 step135
  have step260 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step142 step40
  have step275 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step142 step10
  have step276 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step142 step275
  have step289 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step136 step260
  have step615 : sK0 ≠ sK0 := superpose step289 step276
  subsumption step615 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2900_implies_Equation3105 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2900 G) : Equation3105 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ (X ◇ Y))) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (s ◇ s)) ◇ s)) := by
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
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step24 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step12
  have step25 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose step13 step12
  have step62 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step21 step25
  have step194 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step62 step24
  have step230 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step194
  have step253 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step230 step14
  have step266 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step253
  have step359 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step266 step10
  have step575 : sK0 ≠ (sK0 ◇ sK0) := superpose step359 step11
  subsumption step575 step266


@[equational_result]
theorem Finite.Equation677_and_Equation2903_implies_Equation2912 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2903 G) : Equation2912 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK0) := mod_symm nh
  have step15 (X Y : G) : (Y ◇ (((X ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (Y ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) := by
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
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose step16 step17
  have step27 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X1 := superpose step12 step18
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step18 step18
  have step38 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step18
  have step164 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step17 step24
  have step263 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose step164 step12
  have step277 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step29 step263
  have step284 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step18 step277
  have step345 (X0 : G) :  (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step284 step38
  have step350 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step18 step345
  have step358 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step350
  have step468 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step358 step16
  have step2781 : sK0 ≠ (sK0 ◇ sK0) := superpose step468 step13
  subsumption step2781 step358


@[equational_result]
theorem Finite.Equation677_and_Equation2912_implies_Equation2936 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2912 G) : Equation2936 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step16 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = X1 := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose step9 step17
  have step28 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step12
  have step55 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X0)) := superpose step28 step12
  have step58 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step55
  have step94 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step58 step9
  have step95 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step58 step12
  have step172 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step94 step12
  have step177 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step18 step172
  have step180 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step95 step177
  have step249 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step180 step22
  have step250 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step180 step9
  have step267 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step180 step249
  have step310 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step58 step15
  have step340 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X0)) := superpose step250 step310
  have step364 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step12 step340
  have step407 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose step267 step58
  have step410 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step267 step407
  have step464 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step16 step22
  have step465 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step250 step464
  have step491 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) := superpose step16 step465
  have step507 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step16 step491
  have step517 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose step364 step507
  have step863 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step410 step410
  have step983 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step517 step18
  have step987 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step517 step11
  have step1018 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step863 step983
  have step1049 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step863 step1018
  have step1168 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step410 step987
  have step1280 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step1049 step1168
  have step1695 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step1280 step10
  subsumption step1695 step250


@[equational_result]
theorem Finite.Equation677_and_Equation2936_implies_Equation3056 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2936 G) : Equation3056 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step13
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step11
  have step28 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step9 step12
  have step29 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step14 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step37 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step30 step29
  have step38 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step9 step28
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step37
  have step40 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose step39 step10
  have step54 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))) := superpose step38 step38
  have step59 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step38 step12
  have step60 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step38 step9
  have step61 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step38 step12
  have step66 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step14 step61
  have step67 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose step39 step59
  have step70 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))) := superpose step39 step54
  have step75 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose step39 step66
  have step77 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0)) := superpose step38 step70
  have step81 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step67 step77
  have step82 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step60 step81
  have step83 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose step75 step82
  have step84 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step9 step30
  have step112 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step83 step84
  have step117 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step83 step112
  have step119 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step20 step117
  have step218 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step83 step11
  have step227 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step119 step218
  have step353 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step227 step12
  have step755 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step227 step353
  have step1324 : sK0 ≠ sK0 := superpose step755 step40
  subsumption step1324 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2940_implies_Equation3954 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2940 G) : Equation3954 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := mod_symm nh
  have step16 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step56 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step16 step18
  have step78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step56 step13
  subsumption step78 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3050_implies_Equation3253 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3050 G) : Equation3253 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step12
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step15
  have step20 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step12
  have step21 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step12
  have step23 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step20
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step17 step23
  have step29 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step24 step9
  have step56 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step29 step9
  have step101 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step56 step10
  have step118 : sK0 ≠ (sK0 ◇ sK0) := superpose step56 step101
  subsumption step118 step56


@[equational_result]
theorem Finite.Equation677_and_Equation3053_implies_Equation3058 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3053 G) : Equation3058 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ ((((sK0 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : ((((X ◇ Y) ◇ (X ◇ Y)) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((s ◇ s) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step11 step11
  have step28 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := superpose step17 step17
  have step45 (X0 X1 X2 : G) :  ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := superpose step17 step14
  have step94 (X0 : G) :  sK0 ≠ ((((sK0 ◇ sK0) ◇ X0) ◇ X0) ◇ sK0) := superpose step28 step12
  subsumption step94 step45


@[equational_result]
theorem Finite.Equation677_and_Equation3056_implies_Equation3068 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3056 G) : Equation3068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((((X ◇ Y) ◇ (X ◇ Y)) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((s ◇ s) ◇ Y) ◇ s)) := by
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
  have step18 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) = X1 := superpose step10 step14
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step23 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose step14 step12
  have step80 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step23 step12
  have step83 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose step12 step80
  have step133 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step13 step83
  have step134 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step19 step83
  have step198 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step133 step12
  have step442 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step10 step18
  have step512 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) := superpose step442 step19
  have step523 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step512
  have step613 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step523 step10
  have step625 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step523 step23
  have step629 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step523 step134
  have step632 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step134 step629
  have step636 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step198 step625
  have step651 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose step632 step636
  have step662 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step12 step651
  have step668 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step613 step662
  have step787 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step668 step10
  have step6280 : sK0 ≠ (sK0 ◇ sK0) := superpose step787 step11
  subsumption step6280 step668


@[equational_result]
theorem Finite.Equation677_and_Equation3058_implies_Equation3075 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3058 G) : Equation3075 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose step9 step16
  have step30 (X0 X1 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1))) ◇ X0) = X0 := superpose step21 step9
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step21 step30
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step33 step11
  have step40 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step33 step12
  have step43 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step17 step40
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step35 step43
  have step131 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) ◇ X0)) := superpose step21 step17
  have step153 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step131
  have step160 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose step33 step153
  have step167 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step44 step160
  have step199 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step167 step10
  subsumption step199 step167


@[equational_result]
theorem Finite.Equation677_and_Equation3059_implies_Equation3078 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3059 G) : Equation3078 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step16 (X Y : G) : ((((X ◇ Y) ◇ (X ◇ Y)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ s) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((s ◇ s) ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step12
  have step32 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step19 step18
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step32
  have step47 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step39 step16
  have step92 : sK0 ≠ (sK0 ◇ sK0) := superpose step47 step13
  subsumption step92 step39


@[equational_result]
theorem Finite.Equation677_and_Equation3068_implies_Equation3115 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3068 G) : Equation3115 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step9 step17
  have step66 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) ◇ X0)) := superpose step22 step18
  have step89 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step66
  have step100 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) := superpose step89 step89
  have step115 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose step89 step9
  have step127 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step115
  have step131 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step9 step100
  have step362 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step131 step131
  have step365 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step11 step131
  have step1150 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose step362 step12
  have step1176 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X1 := superpose step18 step1150
  have step1537 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step1176 step131
  have step2141 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step1176 step1537
  have step2170 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose step1537 step365
  have step2173 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose step362 step2170
  have step2212 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step2141 step2173
  have step2581 : sK0 ≠ (sK0 ◇ sK0) := superpose step2212 step10
  subsumption step2581 step127


@[equational_result]
theorem Finite.Equation677_and_Equation3069_implies_Equation2088 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3069 G) : Equation2088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : ((((X ◇ Y) ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((s ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step40 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step13 step15
  have step63 : sK0 ≠ sK0 := superpose step40 step12
  subsumption step63 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation307_implies_Equation326 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation307 G) : Equation326 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step15
  have step24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step20 step10
  subsumption step24 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3075_implies_Equation3459 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3075 G) : Equation3459 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose step9 step18
  have step32 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose step23 step9
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step23 step32
  have step54 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step33 step11
  have step59 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step33 step12
  have step63 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step19 step59
  have step66 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step54 step63
  have step162 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ X0)) := superpose step23 step19
  have step186 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step162
  have step195 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose step33 step186
  have step309 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step195
  have step324 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step195 step12
  have step334 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step195 step324
  have step352 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step309 step334
  have step513 : sK0 ≠ (sK0 ◇ sK0) := superpose step352 step10
  subsumption step513 step66


@[equational_result]
theorem Finite.Equation677_and_Equation3078_implies_Equation4074 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3078 G) : Equation4074 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step9
  have step15 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step9
  have step18 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15 step11
  have step21 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step18
  have step26 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step28 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step15 step12
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step12
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step29
  have step36 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step28
  have step37 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step26
  have step74 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step37
  have step100 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0)) := superpose step35 step74
  have step106 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := superpose step9 step100
  have step107 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step9 step106
  have step167 : sK0 ≠ (sK0 ◇ sK0) := superpose step107 step10
  subsumption step167 step36


@[equational_result]
theorem Finite.Equation677_and_Equation3091_implies_Equation3973 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3091 G) : Equation3973 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 X3 : G) :  (((X0 ◇ X1) ◇ X2) ◇ X1) = (((X0 ◇ X3) ◇ X2) ◇ X3) := superpose step9 step9
  have step16 (X0 X1 X2 : G) :  (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) = X1 := superpose step11 step9
  have step18 (X0 X1 X2 : G) :  (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X2 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose step12 step9
  have step53 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X3) ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step13
  have step87 (X0 X1 X2 : G) :  ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose step11 step16
  have step817 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step9 step18
  have step982 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose step817 step12
  have step993 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) ◇ X0)) := superpose step817 step19
  have step1009 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose step12 step993
  have step1134 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose step1009 step9
  have step1171 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step1009 step9
  have step1174 (X0 X1 : G) :  (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) := superpose step1009 step9
  have step1204 (X0 X1 X2 X3 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = ((X3 ◇ X2) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose step1009 step53
  have step1214 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step1009 step1174
  have step1215 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step1009 step1171
  have step1229 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step1134
  have step1553 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose step21 step87
  have step1764 (X0 X2 : G) :  (X2 ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ X2)) := superpose step1204 step1553
  have step1802 (X0 X2 : G) :  (X2 ◇ X2) = ((X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ X2)) := superpose step1214 step1764
  have step1822 (X0 X2 : G) :  ((X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X2 := superpose step1229 step1802
  have step1832 (X0 X2 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose step982 step1822
  have step1837 (X0 X2 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X2 := superpose step1215 step1832
  have step1838 (X0 X2 : G) :  (X0 ◇ (X0 ◇ X2)) = X2 := superpose step1229 step1837
  have step1857 (X0 X1 X2 : G) :  (X1 ◇ ((X2 ◇ X1) ◇ X2)) = ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X0) := superpose step87 step1838
  have step1884 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step1838 step12
  have step1955 (X0 X1 X2 : G) :  (X1 ◇ ((X2 ◇ X1) ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose step1884 step1857
  have step1983 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose step1884 step1955
  have step61214 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step1983 step10
  subsumption step61214 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3105_implies_Equation3140 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3105 G) : Equation3140 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step9 step9
  have step18 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X0 := superpose step9 step18
  have step25 (X0 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step14 step12
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step14 step25
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step29
  have step40 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = (((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose step23 step9
  have step41 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose step23 step40
  have step49 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose step30 step41
  have step53 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X0 := superpose step23 step49
  have step58 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step30 step10
  have step149 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) ◇ X0)) := superpose step23 step53
  have step166 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := superpose step12 step149
  have step176 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step53 step166
  have step265 : sK0 ≠ sK0 := superpose step176 step58
  subsumption step265 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3113_implies_Equation3342 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3113 G) : Equation3342 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ Y) ◇ s)) := by
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
  have step15 (X0 X1 : G) :  (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose step10 step10
  have step19 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose step12 step12
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step39 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step14 step19
  have step40 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step26 step19
  have step55 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step12 step40
  have step56 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose step12 step39
  have step84 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step55 step14
  have step116 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step15 step10
  have step125 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step84 step116
  have step143 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose step125 step11
  have step144 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose step125 step143
  have step825 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step56 step13
  have step1053 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step825 step56
  have step1054 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step56 step1053
  have step1298 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step1054 step12
  have step1323 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step12 step1298
  have step1572 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step1323 step14
  have step1596 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step14 step1572
  have step2234 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step1596 step144
  subsumption step2234 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3115_implies_Equation3143 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3115 G) : Equation3143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step22 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose step9 step17
  have step28 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step12
  have step52 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) ◇ X0)) := superpose step28 step12
  have step55 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step52
  have step94 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := superpose step55 step55
  have step108 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose step55 step9
  have step120 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step9 step108
  have step125 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step9 step94
  have step225 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := superpose step120 step10
  subsumption step225 step125


@[equational_result]
theorem Finite.Equation677_and_Equation3116_implies_Equation1289 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3116 G) : Equation1289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ (((X ◇ Y) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step13 step14


@[equational_result]
theorem Finite.Equation677_and_Equation3140_implies_Equation3352 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3140 G) : Equation3352 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ Y) ◇ s) ◇ s)) := by
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
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose step12 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step27 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step14 step12
  have step44 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step27 step14
  have step49 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step44
  have step50 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step49 step14
  have step52 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step49 step14
  have step53 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step49 step12
  have step55 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step53
  have step56 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step25 step52
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step55 step56
  have step60 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step26 step12
  have step63 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step57 step60
  have step66 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step18 step63
  have step67 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step50 step66
  have step80 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step67 step11
  have step88 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose step14 step18
  have step122 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step67 step88
  have step137 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step122
  have step728 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step137 step18
  have step733 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step728
  have step757 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step67 step733
  have step943 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step757 step80
  subsumption step943 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3143_implies_Equation3261 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3143 G) : Equation3261 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : (sK0 ◇ sK0) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) := by
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
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step15 step11
  have step38 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step14
  have step47 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step38 step16
  have step54 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step47
  have step78 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step54 step14
  have step79 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step54 step13
  have step119 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step78 step78
  have step121 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step15 step78
  have step126 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step78 step15
  have step136 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step126 step121
  have step143 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose step119 step136
  have step190 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step79 step16
  have step197 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step126 step190
  have step340 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step79 step29
  have step381 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step119 step340
  have step402 (X0 X1 : G) :  ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = X0 := superpose step143 step381
  have step421 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := superpose step197 step402
  have step438 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step197 step421
  have step449 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step54 step438
  have step490 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step449 step12
  subsumption step490 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation315_implies_Equation419 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation315 G) : Equation419 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step9 step9
  have step16 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step9 step10
  have step17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step16
  have step18 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step17
  have step64 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) = X1 := superpose step9 step12
  have step66 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose step13 step12
  have step78 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step66 step64
  have step86 : sK0 ≠ sK0 := superpose step78 step18
  subsumption step86 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3253_implies_Equation3319 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3253 G) : Equation3319 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step15
  have step24 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step20 step10
  subsumption step24 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3261_implies_Equation3278 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3261 G) : Equation3278 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step12 step18
  have step33 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step24 step10
  subsumption step33 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation326_implies_Equation359 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation326 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step26 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step12 step18
  have step31 : sK0 ≠ (sK0 ◇ sK0) := superpose step26 step10
  subsumption step31 step26


@[equational_result]
theorem Finite.Equation677_and_Equation3278_implies_Equation3306 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3278 G) : Equation3306 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step9 step12
  have step17 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step9 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose step17 step12
  have step29 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step27
  have step32 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step17 step15
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step15 step12
  have step40 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step32
  have step41 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step29 step40
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step34 step11
  have step49 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step41 step47
  have step50 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step34 step49
  have step81 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step50 step9
  have step144 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step81 step10
  subsumption step144 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3281_implies_Equation75 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3281 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step9 step9
  have step17 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step22 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step23 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step16 step22
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := superpose step16 step23
  have step160 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step16 step24
  have step171 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step160
  have step280 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step171 step12
  have step295 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step280
  have step379 : sK0 ≠ sK0 := superpose step295 step17
  subsumption step379 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3306_implies_Equation3334 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3306 G) : Equation3334 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step11 step9
  have step39 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step17 step10
  subsumption step39 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3319_implies_Equation3456 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3319 G) : Equation3456 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step24 (X1 : G) :  (X1 ◇ (X1 ◇ X1)) = X1 := superpose step12 step18
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step24 step12
  have step45 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step26 step9
  have step47 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step26 step11
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step47
  have step52 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step45 step48
  have step54 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step26 step52
  have step83 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step54 step10
  subsumption step83 step24


@[equational_result]
theorem Finite.Equation677_and_Equation332_implies_Equation476 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation332 G) : Equation476 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose step9 step13
  have step15 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step9 step14
  have step32 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step11 step15
  have step33 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := superpose step9 step32
  have step40 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step15 step33
  have step337 : sK0 ≠ sK0 := superpose step40 step10
  subsumption step337 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3334_implies_Equation3414 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3334 G) : Equation3414 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 X2 : G) :  (X2 ◇ (X2 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step28 (X1 X2 : G) :  (X2 ◇ (X2 ◇ X1)) = X1 := superpose step12 step20
  have step37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step28 step10
  subsumption step37 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3342_implies_Equation3545 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3342 G) : Equation3545 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step13
  have step18 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step47 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step18
  have step56 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step18 step12
  have step63 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step14 step47
  have step73 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step63
  have step79 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step73
  have step83 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step56 step79
  have step89 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose step83 step9
  have step94 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose step83 step10
  have step95 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose step83 step94
  have step100 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step83 step89
  have step426 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step100 step95
  subsumption step426 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation335_implies_Equation1239 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation335 G) : Equation1239 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step9 step9
  have step17 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := superpose step11 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose step13 step18
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step13 step17
  have step23 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step20
  have step25 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step13 step23
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step25
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step27
  have step31 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step29
  have step33 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step42 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step13 step34
  have step43 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step13 step33
  have step47 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step13 step42
  have step51 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step13 step47
  have step53 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step51
  have step69 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step13 step11
  have step152 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose step19 step9
  have step155 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step19 step13
  have step160 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose step69 step155
  have step162 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X1 := superpose step69 step152
  have step177 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step13 step160
  have step759 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ X1)) = X0 := superpose step19 step162
  have step769 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step162 step43
  have step783 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step177 step769
  have step793 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose step69 step759
  have step825 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step53 step783
  have step831 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X0 ◇ X1)) = X0 := superpose step13 step793
  have step851 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose step825 step831
  have step1311 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose step69 step851
  have step1386 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose step19 step1311
  have step1428 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose step13 step1386
  have step1462 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step9 step1428
  have step1826 : sK0 ≠ (sK0 ◇ sK0) := superpose step1462 step10
  subsumption step1826 step31


@[equational_result]
theorem Finite.Equation677_and_Equation3352_implies_Equation3558 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3352 G) : Equation3558 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step30 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step33 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step30
  have step40 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step33 step12
  have step42 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step40
  have step82 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step42 step10
  have step86 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step42 step9
  subsumption step82 step86


@[equational_result]
theorem Finite.Equation677_and_Equation3353_implies_Equation1691 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3353 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step77 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step9 step19
  have step97 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose step20 step77
  have step100 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose step9 step97
  have step115 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step100 step19
  have step121 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step12 step115
  have step175 : sK0 ≠ sK0 := superpose step121 step10
  subsumption step175 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3414_implies_Equation3475 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3414 G) : Equation3475 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step19 (X0 X2 : G) :  (X2 ◇ (X2 ◇ X0)) = X0 := superpose step11 step9
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step29 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step19 step25
  have step59 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step29 step18
  have step65 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step29 step10
  have step66 : sK0 ≠ (sK0 ◇ sK0) := superpose step19 step65
  subsumption step66 step59


@[equational_result]
theorem Finite.Equation677_and_Equation3456_implies_Equation3522 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3456 G) : Equation3522 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step16
  have step29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step21 step10
  subsumption step29 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3459_implies_Equation3518 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3459 G) : Equation3518 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step12 step18
  have step37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step24 step10
  subsumption step37 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3475_implies_Equation3484 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3475 G) : Equation3484 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) = X1 := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step14 step16
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step41 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step19 step21
  have step52 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step19 step41
  have step57 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step52
  have step60 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step57 step10
  have step62 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step57 step9
  have step70 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step57 step60
  have step217 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2)) := superpose step13 step12
  have step222 (X1 X2 : G) :  ((X1 ◇ X2) ◇ X2) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step62 step217
  have step1055 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step222 step12
  have step1343 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step1055 step17
  have step1348 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step1055 step62
  have step1356 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) := superpose step57 step1343
  have step1387 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step1055 step1356
  have step1399 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step1348 step1387
  have step1431 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step24 step18
  have step1529 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step1348 step1431
  have step1592 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step11 step1529
  have step1642 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step1399 step1592
  have step1739 : sK0 ≠ sK0 := superpose step1642 step70
  subsumption step1739 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3481_implies_Equation3865 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3481 G) : Equation3865 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step16 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step16 step9
  have step28 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step27
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step28
  have step55 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step30 step18
  have step64 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) := superpose step18 step12
  have step69 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) := superpose step30 step64
  have step78 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step55 step69
  have step199 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step55 step12
  have step203 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step55 step11
  have step244 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step19 step12
  have step265 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step55 step244
  have step281 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose step55 step265
  have step454 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step199 step199
  have step654 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step454 step203
  have step4041 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step654 step281
  have step4138 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step78 step4041
  have step4178 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step454 step4138
  have step4202 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step199 step4178
  have step4278 : sK0 ≠ (sK0 ◇ sK0) := superpose step4202 step10
  subsumption step4278 step30


@[equational_result]
theorem Finite.Equation677_and_Equation3484_implies_Equation3548 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3484 G) : Equation3548 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X2 ◇ ((X2 ◇ X2) ◇ X1)) := superpose step9 step9
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step12
  have step30 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step19 step11
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step30
  have step32 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step28 step31
  have step57 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step32 step9
  have step66 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step32 step57
  have step110 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2)) := superpose step13 step12
  have step113 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose step32 step110
  have step145 (X1 X2 : G) :  ((X2 ◇ X2) ◇ X1) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step66 step113
  have step175 (X1 X2 : G) :  (X2 ◇ X1) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step32 step145
  have step2531 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step175 step10
  subsumption step2531 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3518_implies_Equation3526 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3518 G) : Equation3526 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step12 step18
  have step37 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step24 step10
  subsumption step37 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3522_implies_Equation3715 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3522 G) : Equation3715 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step23 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step30 (X1 : G) :  ((X1 ◇ X1) ◇ X1) = X1 := superpose step12 step23
  have step41 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step30 step12
  have step44 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step24 step41
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step44
  have step60 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step48 step10
  have step61 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step48 step60
  subsumption step61 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3526_implies_Equation3668 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3526 G) : Equation3668 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step22 (X0 X1 X2 : G) :  ((X1 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step12
  have step30 (X1 X2 : G) :  ((X1 ◇ X2) ◇ X2) = X1 := superpose step12 step22
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step20 step12
  have step52 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step32 step30
  have step59 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step52
  have step102 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step59 step10
  have step103 : sK0 ≠ (sK0 ◇ sK0) := superpose step30 step102
  subsumption step103 step59


@[equational_result]
theorem Finite.Equation677_and_Equation3545_implies_Equation3749 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3545 G) : Equation3749 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step14
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step11 step15
  have step22 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step28 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step34 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step17 step28
  have step36 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step22 step34
  have step37 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step36
  have step39 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose step37 step9
  have step46 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step37 step39
  have step79 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose step46 step10
  subsumption step79 step37


@[equational_result]
theorem Finite.Equation677_and_Equation3548_implies_Equation3675 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3548 G) : Equation3675 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step17
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step27 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step12 step9
  have step28 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step16 step27
  have step29 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step16 step26
  have step33 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step28 step29
  have step59 : sK0 ≠ (sK0 ◇ sK0) := superpose step18 step10
  have step78 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step33 step9
  have step87 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step78
  have step105 : sK0 ≠ sK0 := superpose step87 step59
  subsumption step105 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3558_implies_Equation3761 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3558 G) : Equation3761 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step22
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step16 step9
  have step29 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step11
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step29
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step25 step26
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step31
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step16 step32
  have step42 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step33 step12
  have step45 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step21 step42
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step45
  have step52 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose step25 step9
  have step57 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step30 step52
  have step63 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step46 step57
  have step66 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step46 step10
  subsumption step66 step63


@[equational_result]
theorem Finite.Equation677_and_Equation359_implies_Equation375 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation359 G) : Equation375 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step18
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step9 step16
  have step31 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step12
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step31
  have step51 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step17
  have step67 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step51
  have step72 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step67
  have step74 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step72
  have step76 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step74 step17
  have step81 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step76
  have step83 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step81
  have step97 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step33 step14
  have step126 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step9 step97
  have step140 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step33 step126
  have step153 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step83 step140
  have step161 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step21 step153
  have step165 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step83 step161
  have step173 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step165 step15
  have step263 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step173 step10
  subsumption step263 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation362_implies_Equation617 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation362 G) : Equation617 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step9 step10
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step24 : sK0 ≠ sK0 := superpose step20 step16
  subsumption step24 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3662_implies_Equation3665 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3662 G) : Equation3665 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step26 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step20
  have step27 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step9 step26
  have step40 (X0 : G) :  (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose step27 step10
  subsumption step40 step27


@[equational_result]
theorem Finite.Equation677_and_Equation3665_implies_Equation3677 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3665 G) : Equation3677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step11 step9
  have step30 (X0 : G) :  (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose step17 step10
  subsumption step30 step17


@[equational_result]
theorem Finite.Equation677_and_Equation3667_implies_Equation159 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3667 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step21 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step11 step9
  have step68 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose step21 step12
  have step2651 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step68 step12
  have step2823 (X0 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step2651 step12
  have step2860 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step2651 step2823
  have step2887 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step2860
  have step3236 : sK0 ≠ sK0 := superpose step2887 step15
  subsumption step3236 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3668_implies_Equation3871 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3668 G) : Equation3871 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) := superpose step9 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step16
  have step23 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step24
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step27 step11
  have step40 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step20 step37
  have step43 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step23 step40
  have step75 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step43 step12
  have step78 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step75
  have step103 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step19 step9
  have step116 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose step78 step103
  have step135 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step78 step116
  have step145 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step78 step135
  have step167 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step78 step10
  have step168 : sK0 ≠ (sK0 ◇ sK0) := superpose step145 step167
  subsumption step168 step78


@[equational_result]
theorem Finite.Equation677_and_Equation3675_implies_Equation3687 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3675 G) : Equation3687 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step14
  have step20 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step15 step20
  have step22 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step210 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15 step22
  have step227 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step21 step210
  have step332 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step227 step12
  have step343 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step12 step332
  have step446 (X0 : G) :  (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step343 step12
  have step461 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step343 step446
  have step470 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step461
  have step578 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step470 step10
  have step597 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step470 step22
  have step621 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step470 step578
  have step2223 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step23 step597
  have step2232 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step597 step11
  have step2264 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step597 step2223
  have step2300 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step597 step2264
  have step2864 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step23 step2232
  have step2959 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose step597 step2864
  have step3031 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose step2300 step2959
  have step3074 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step2232 step3031
  have step3587 : sK0 ≠ sK0 := superpose step3074 step621
  subsumption step3587 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3677_implies_Equation3684 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3677 G) : Equation3684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step9 step16
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step9 step17
  have step40 (X0 : G) :  (X0 ◇ X0) ≠ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := superpose step18 step10
  have step54 : (sK1 ◇ sK1) ≠ (sK1 ◇ sK1) := superpose step9 step40
  subsumption step54 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3684_implies_Equation4270 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3684 G) : Equation4270 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose step9 step15
  have step20 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step9 step19
  have step21 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step9 step20
  have step47 (X0 : G) :  (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ X0)) := superpose step21 step10
  subsumption step47 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3687_implies_Equation3881 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3687 G) : Equation3881 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 X2 : G) :  (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step9 step9
  have step27 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step9 step12
  have step49 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step16 step12
  have step52 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose step27 step49
  have step78 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step19 step16
  have step81 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step19 step9
  have step83 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose step19 step12
  have step88 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step27 step83
  have step90 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step52 step81
  have step92 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step52 step78
  have step104 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose step52 step90
  have step105 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step88 step92
  have step114 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose step52 step104
  have step125 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose step9 step52
  have step175 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose step52 step125
  have step572 (X0 X1 X2 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) := superpose step12 step15
  have step662 (X0 X1 X2 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = ((X2 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) := superpose step52 step572
  have step742 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step175 step662
  have step809 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step105 step742
  have step864 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step175 step809
  have step1990 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step864 step864
  have step11979 : (sK0 ◇ sK0) ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step1990 step10
  have step12050 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step864 step11979
  subsumption step12050 step114


@[equational_result]
theorem Finite.Equation677_and_Equation3715_implies_Equation3722 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3715 G) : Equation3722 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step9 step14
  have step16 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step9 step13
  have step25 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step15 step11
  have step31 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step16 step25
  have step35 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step11 step31
  have step41 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step35 step10
  subsumption step41 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3722_implies_Equation3862 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3722 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step9
  have step29 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step16 step10
  have step35 : sK0 ≠ (sK0 ◇ sK0) := superpose step16 step29
  subsumption step35 step16


@[equational_result]
theorem Finite.Equation677_and_Equation3748_implies_Equation3951 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3748 G) : Equation3951 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step13
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step15 step22
  have step52 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step18 step15
  have step59 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step15 step14
  have step69 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step9 step52
  have step77 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step15 step69
  have step82 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step77
  have step87 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step25 step15
  have step96 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step87
  have step104 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step96
  have step108 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step82 step104
  have step111 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step15 step108
  have step113 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step59 step111
  have step114 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step18 step113
  have step119 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step114 step25
  have step125 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step119
  have step228 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step125 step14
  have step236 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose step125 step10
  have step1027 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step228 step236
  subsumption step1027 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3749_implies_Equation3751 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3749 G) : Equation3751 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step21 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose step9 step17
  have step22 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step9 step21
  have step35 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step22 step10
  subsumption step35 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3751_implies_Equation3964 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3751 G) : Equation3964 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step25 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step13
  have step27 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step13 step9
  have step76 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose step25 step10
  have step86 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose step27 step76
  have step90 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step25 step86
  subsumption step90 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation375_implies_Equation1629 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation375 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := superpose step9 step10
  have step16 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step15
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step11 step9
  have step25 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step24
  have step31 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step21 step9
  have step34 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step31
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step34
  have step64 : sK0 ≠ (sK0 ◇ sK0) := superpose step39 step16
  subsumption step64 step39


@[equational_result]
theorem Finite.Equation677_and_Equation3761_implies_Equation4081 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3761 G) : Equation4081 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step14
  have step16 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose step9 step11
  have step19 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose step11 step9
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose step12 step9
  have step28 (X0 : G) :  (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step19 step12
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step19 step28
  have step35 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step22 step33
  have step40 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step13 step13
  have step59 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step35 step12
  have step113 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step35 step20
  have step114 (X0 : G) :  (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step19 step20
  have step116 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step20 step20
  have step127 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step13 step116
  have step128 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step40 step114
  have step129 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step25 step113
  have step133 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step128
  have step134 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step129
  have step137 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step11 step133
  have step138 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step12 step134
  have step139 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step127 step137
  have step166 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step138 step12
  have step171 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step22 step166
  have step174 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step40 step171
  have step177 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step40 step174
  have step178 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step13 step177
  have step179 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step15 step178
  have step180 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step179
  have step201 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose step35 step16
  have step229 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step59 step201
  have step252 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step139 step229
  have step261 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step180 step252
  have step265 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step261
  have step268 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step15 step265
  have step271 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step268
  have step273 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step180 step271
  have step276 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step273 step13
  have step277 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step273 step15
  have step689 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step276 step12
  have step1203 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := superpose step25 step276
  have step1229 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step273 step1203
  have step1276 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step277 step1229
  have step1317 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step277 step1276
  have step1353 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step276 step1317
  have step1384 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step689 step1353
  have step1443 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step25 step277
  have step1530 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step12 step1443
  have step1566 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step277 step1530
  have step1591 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step277 step1566
  have step1605 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step276 step1591
  have step1612 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step273 step1605
  have step1615 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step1384 step1612
  have step1967 : sK0 ≠ (sK0 ◇ sK0) := superpose step1615 step10
  subsumption step1967 step273


@[equational_result]
theorem Finite.Equation677_and_Equation384_implies_Equation3748 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation384 G) : Equation3748 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step16 step9
  have step39 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step13 step38
  have step42 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step16 step39
  have step43 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step42
  have step52 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step9
  have step58 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step43 step52
  have step72 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose step58 step10
  subsumption step72 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3862_implies_Equation3915 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3862 G) : Equation3915 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step21 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step17 step16
  have step26 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step21
  have step29 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step21 step12
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step21 step29
  have step43 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step31 step12
  have step44 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step31 step12
  have step46 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step44 step43
  have step47 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step18 step46
  have step54 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step47 step21
  have step68 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step54 step17
  have step99 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step26 step68
  have step102 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step99
  have step107 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step102 step10
  have step134 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step102 step107
  subsumption step134 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3865_implies_Equation124 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3865 G) : Equation124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step11 step9
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step9
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step21
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step22 step25
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step26 step9
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step26 step30
  have step33 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step31
  have step106 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step18
  have step125 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose step33 step106
  have step155 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step12 step125
  have step170 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) := superpose step125 step12
  have step302 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step12 step155
  have step332 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step20
  have step336 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step155 step20
  have step391 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step11 step336
  have step394 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step33 step332
  have step400 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step170 step391
  have step406 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step302 step302
  have step604 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose step406 step406
  have step629 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose step406 step302
  have step630 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose step394 step629
  have step646 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose step400 step604
  have step660 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step12 step646
  have step667 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step400 step660
  have step671 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step400 step667
  have step915 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step125 step24
  have step965 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step915
  have step997 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose step33 step965
  have step1444 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose step12 step671
  have step1601 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose step23 step20
  have step1616 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step12 step1601
  have step1654 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step630 step1616
  have step1714 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step997 step1444
  have step1717 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step155 step1444
  have step1828 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step11 step1717
  have step1831 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) ◇ X0) := superpose step1444 step1714
  have step1857 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step1831
  have step1927 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step1654 step12
  have step1935 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step1654 step997
  have step1976 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step394 step1935
  have step2030 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step1857 step1976
  have step2057 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step1927 step2030
  have step2150 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step2057 step1444
  have step2152 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step1828 step2150
  have step2458 : sK0 ≠ sK0 := superpose step2152 step10
  subsumption step2458 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3868_implies_Equation209 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3868 G) : Equation209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step25 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step21
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step25
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step25 step12
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step25 step33
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step31 step37
  have step57 : sK0 ≠ sK0 := superpose step38 step14
  subsumption step57 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3871_implies_Equation4068 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3871 G) : Equation4068 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step27 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := superpose step9 step24
  have step29 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step9
  have step35 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := superpose step29 step27
  have step36 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step29 step35
  have step52 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step29 step10
  subsumption step52 step36


@[equational_result]
theorem Finite.Equation677_and_Equation3881_implies_Equation3887 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3881 G) : Equation3887 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step21 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1)) = X1 := superpose step9 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step28 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose step14 step21
  have step31 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose step25 step9
  have step53 (X0 X1 X2 : G) :  ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) ◇ X2) = X1 := superpose step9 step31
  have step156 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0))) := superpose step16 step9
  have step160 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0))) := superpose step16 step13
  have step162 (X0 X1 X2 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0))) := superpose step53 step160
  have step164 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0))) := superpose step53 step156
  have step174 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose step16 step162
  have step176 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step164
  have step191 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step176 step19
  have step252 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step174 step174
  have step278 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step174 step12
  have step286 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose step191 step278
  have step347 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := superpose step28 step12
  have step351 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose step28 step19
  have step354 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X0 := superpose step176 step351
  have step358 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose step191 step347
  have step378 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := superpose step252 step354
  have step382 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose step252 step358
  have step400 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step378 step382
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step400 step286
  have step1031 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step719 step10
  subsumption step1031 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3887_implies_Equation3962 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3887 G) : Equation3962 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step9 step11
  have step16 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step27 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step9
  have step39 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step27 step11
  have step144 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step16
  have step152 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step18 step144
  have step154 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step39 step152
  have step177 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step20
  have step192 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step154 step20
  have step208 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step192
  have step219 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step20 step177
  have step220 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step208
  have step227 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step9 step219
  have step231 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step220 step227
  have step233 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step9 step231
  have step234 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step220 step233
  have step248 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose step220 step14
  have step262 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step234 step248
  have step703 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step262 step10
  subsumption step703 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation8 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3915_implies_Equation4118 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3915 G) : Equation4118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step11 step9
  have step25 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step24
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step34 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step12 step9
  have step39 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step32 step9
  have step72 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step39 step10
  have step200 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step25 step12
  have step204 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step25 step12
  have step209 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step204 step200
  have step228 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step31 step209
  have step267 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step34 step12
  have step269 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step12 step267
  have step319 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step32 step31
  have step332 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step228 step319
  have step337 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step39 step332
  have step340 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step32 step269
  have step366 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step337 step340
  have step377 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step228 step366
  have step387 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step39 step377
  have step392 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step32 step387
  have step573 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step392 step72
  subsumption step573 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3951_implies_Equation4130 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3951 G) : Equation4130 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step20 step9
  have step36 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step22 step12
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step36
  have step57 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step38 step9
  have step415 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose step57 step10
  subsumption step415 step57


@[equational_result]
theorem Finite.Equation677_and_Equation3954_implies_Equation707 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3954 G) : Equation707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose step19 step18
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step24 step24
  have step420 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step32 step24
  have step564 : sK0 ≠ sK0 := superpose step420 step10
  subsumption step564 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3962_implies_Equation4023 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3962 G) : Equation4023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step27 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step20
  have step37 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose step11 step22
  have step42 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step18 step37
  have step63 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step42 step12
  have step67 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step27 step63
  have step169 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step67 step10
  subsumption step169 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3964_implies_Equation4167 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3964 G) : Equation4167 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X1) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X1) := superpose step9 step14
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step9 step15
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step42 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step34
  have step47 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step42
  have step48 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step34 step47
  have step98 : (sK0 ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := superpose step17 step10
  have step99 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step48 step98
  subsumption step99 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3973_implies_Equation1098 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3973 G) : Equation1098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  have step19 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ X0) := superpose step11 step9
  have step26 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose step9 step19
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step40 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step48 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step39
  have step65 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := superpose step19 step40
  have step67 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose step40 step9
  have step69 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step40 step19
  have step73 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step26 step69
  have step75 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step26 step65
  have step80 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step73 step75
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := superpose step19 step48
  have step99 (X1 : G) :  (X1 ◇ X1) = X1 := superpose step80 step83
  have step206 : sK0 ≠ (sK0 ◇ sK0) := superpose step67 step15
  subsumption step206 step99


@[equational_result]
theorem Finite.Equation677_and_Equation4023_implies_Equation4071 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4023 G) : Equation4071 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step11
  have step24 (X0 X1 X2 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose step11 step9
  have step27 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step24 step18
  have step29 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step19 step27
  have step30 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X0)))) = X1 := superpose step9 step12
  have step31 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step24 step33
  have step45 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step29 step31
  have step46 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := superpose step29 step30
  have step47 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step34 step43
  have step49 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step45
  have step50 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step9 step46
  have step51 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step9 step47
  have step57 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose step49 step51
  have step58 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose step9 step57
  have step59 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step50 step58
  have step98 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step50 step34
  have step238 : sK0 ≠ (sK0 ◇ sK0) := superpose step98 step10
  subsumption step238 step59


@[equational_result]
theorem Finite.Equation677_and_Equation40_implies_Equation280 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation40 G) : Equation280 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 : G) :  sK0 ≠ (((X0 ◇ X0) ◇ sK0) ◇ sK0) := superpose step9 step10
  have step32 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step9 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step62 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := superpose step34 step32
  have step988 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step62 step12
  have step994 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X0 := superpose step34 step988
  have step1065 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := superpose step994 step12
  have step1073 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := superpose step994 step1065
  have step1740 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X0)) := superpose step1073 step34
  have step1744 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step12 step1740
  have step2671 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step1744 step994
  have step3055 : sK0 ≠ sK0 := superpose step2671 step18
  subsumption step3055 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4068_implies_Equation4127 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4068 G) : Equation4127 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose step11 step9
  have step20 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step12 step9
  have step23 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step20 step12
  have step25 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step23
  have step35 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step25 step12
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step25 step35
  have step39 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step12 step16
  have step55 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step25 step39
  have step58 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step37 step55
  have step66 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step58 step9
  have step144 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step66 step10
  subsumption step144 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4071_implies_Equation4084 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4071 G) : Equation4084 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose step9 step11
  have step16 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step9
  have step31 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step16 step12
  have step50 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step14
  have step57 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step18
  have step69 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose step18 step9
  have step92 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step50 step12
  have step96 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step50 step18
  have step97 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step12 step96
  have step100 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step17 step92
  have step103 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step57 step97
  have step106 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step31 step103
  have step107 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step100 step106
  have step165 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step107 step12
  have step178 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step100 step165
  have step185 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step107 step178
  have step278 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step16 step21
  have step329 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step185 step278
  have step344 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose step185 step329
  have step758 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step69 step69
  have step781 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step69 step18
  have step786 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step185 step781
  have step807 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose step185 step758
  have step819 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose step12 step786
  have step831 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step12 step807
  have step844 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step185 step831
  have step966 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0))) := superpose step344 step12
  have step989 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step844 step966
  have step1055 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step11 step989
  have step1199 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step1055 step1055
  have step1200 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step18 step1055
  have step1211 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step1055 step18
  have step1260 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step819 step1200
  have step1261 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step1211 step1199
  have step2768 : (sK0 ◇ sK0) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step1261 step10
  have step2815 : sK0 ≠ (sK0 ◇ sK0) := superpose step1260 step2768
  subsumption step2815 step185


@[equational_result]
theorem Finite.Equation677_and_Equation4074_implies_Equation1232 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4074 G) : Equation1232 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step10
  have step19 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose step9 step11
  have step124 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0))) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0))) := superpose step19 step9
  have step132 (X0 X1 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0))) := superpose step19 step124
  have step141 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step19 step132
  have step161 : sK0 ≠ (sK0 ◇ sK0) := superpose step141 step17
  subsumption step161 step141


@[equational_result]
theorem Finite.Equation677_and_Equation4081_implies_Equation4290 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4081 G) : Equation4290 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step9 step9
  have step14 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step32 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step13
  have step33 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step14 step13
  have step44 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step13 step12
  have step92 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step19
  have step93 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose step9 step19
  have step98 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step19
  have step108 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step19 step9
  have step116 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step98
  have step178 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step33 step12
  have step185 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step44 step178
  have step272 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X1) := superpose step9 step185
  have step277 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step185
  have step300 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step185 step19
  have step301 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step18 step300
  have step316 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step185 step277
  have step1002 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step32 step21
  have step1031 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step316 step1002
  have step1058 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step116 step1031
  have step1134 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step1058 step19
  have step1141 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step1134
  have step1149 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step1141
  have step1168 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step1058 step108
  have step1211 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step1168
  have step1228 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step12 step1211
  have step1240 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step92 step1228
  have step1245 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step1149 step1240
  have step1250 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step1245
  have step1272 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1250 step12
  have step1305 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step1272
  have step1548 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ sK0) := superpose step1305 step10
  have step4472 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))))) := superpose step93 step16
  have step4497 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step1305 step4472
  have step4565 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step12 step4497
  have step4609 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step11 step4565
  have step4774 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) := superpose step4609 step301
  have step4781 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) := superpose step272 step4774
  have step4855 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose step1305 step4781
  have step4898 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose step1305 step4855
  have step5311 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose step4898 step18
  have step5348 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step18 step5311
  have step5836 : (sK1 ◇ sK0) ≠ (sK1 ◇ sK0) := superpose step5348 step1548
  subsumption step5836 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4084_implies_Equation4275 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4084 G) : Equation4275 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X1) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step9 step9
  have step17 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X0 ◇ X1) ◇ X1) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1)) = X1 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step9 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step84 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step14
  have step426 (X0 : G) :  (X0 ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step23 step20
  have step464 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step84 step426
  have step471 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step464
  have step475 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step471 step17
  have step511 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step11 step475
  have step569 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step21 step15
  have step574 (X0 X1 : G) :  ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step21 step19
  have step583 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step471 step574
  have step588 (X0 X1 : G) :  (X1 ◇ X1) = (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step471 step569
  have step625 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X1) := superpose step471 step583
  have step629 (X0 X1 : G) :  (X1 ◇ X1) = ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step471 step588
  have step662 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step511 step625
  have step666 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step511 step629
  have step688 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose step511 step662
  have step691 (X0 X1 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step471 step666
  have step707 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step688 step691
  have step744 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step707 step10
  subsumption step744 step707


@[equational_result]
theorem Finite.Equation677_and_Equation411_implies_Equation4380 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation411 G) : Equation4380 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step15 step12
  have step23 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step21
  have step30 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step23 step10
  subsumption step30 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4118_implies_Equation4470 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4118 G) : Equation4470 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step9 step20
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step29 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step12 step9
  have step36 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step17 step12
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step25 step36
  have step58 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose step21 step12
  have step59 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step21 step12
  have step61 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step59 step58
  have step67 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step27 step61
  have step73 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step38
  have step79 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step73
  have step81 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step11 step79
  have step83 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step81
  have step108 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step83 step11
  have step129 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step29 step11
  have step130 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step67 step129
  have step136 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step130
  have step142 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step108 step136
  have step148 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step108 step142
  have step156 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose step148 step10
  have step176 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step148 step156
  subsumption step176 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4127_implies_Equation4135 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4127 G) : Equation4135 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK2) ◇ sK2) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step11 step9
  have step27 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step16 step10
  subsumption step27 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4130_implies_Equation4164 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4130 G) : Equation4164 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step9
  have step14 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = X0 := superpose step11 step9
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step14 step12
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step24
  have step43 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step17 step9
  have step58 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := superpose step27 step10
  have step370 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0)) := superpose step43 step19
  have step373 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step13 step19
  have step428 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step12 step373
  have step431 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step12 step370
  have step470 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X0 := superpose step428 step9
  have step495 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step431 step470
  have step1129 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose step18 step495
  have step1178 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := superpose step12 step1129
  have step1631 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step1178 step58
  subsumption step1631 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4135_implies_Equation4146 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4135 G) : Equation4146 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X2) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK2) ◇ sK2) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X2 : G) :  ((X0 ◇ X2) ◇ X2) = X0 := superpose step11 step9
  have step33 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step17 step10
  subsumption step33 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4146_implies_Equation4383 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4146 G) : Equation4383 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ X1) = (((X0 ◇ X2) ◇ X2) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step11
  have step20 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) := superpose step11 step9
  have step21 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := superpose step11 step9
  have step22 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := superpose step9 step21
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step9 step26
  have step42 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step17
  have step49 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step34 step42
  have step110 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step49 step12
  have step117 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step110
  have step198 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose step117 step20
  have step201 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step117 step9
  have step204 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step201
  have step206 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose step117 step198
  have step240 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step34 step17
  have step251 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step49 step240
  have step265 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step206 step251
  have step278 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose step265 step22
  have step285 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step204 step278
  have step595 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) := superpose step285 step9
  have step600 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose step9 step595
  have step627 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step285 step600
  have step797 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step627 step10
  subsumption step797 step117


@[equational_result]
theorem Finite.Equation677_and_Equation4164_implies_Equation4479 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4164 G) : Equation4479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step16 step9
  have step32 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step16 step29
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step32
  have step81 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step19
  have step194 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step13 step18
  have step236 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step194 step12
  have step245 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step236
  have step306 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step245 step9
  have step316 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step306
  have step439 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step316 step19
  have step441 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step18 step439
  have step576 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step245 step41
  have step578 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step41 step12
  have step593 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step245 step578
  have step602 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step441 step593
  have step607 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step602
  have step636 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step607 step11
  have step654 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step607 step9
  have step671 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step607 step654
  have step687 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step245 step81
  have step786 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step671 step687
  have step806 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step576 step786
  have step819 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step18 step806
  have step849 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step819 step16
  have step915 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step636 step849
  have step1158 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step915 step9
  have step2368 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose step1158 step10
  have step2369 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step915 step2368
  subsumption step2369 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4167_implies_Equation4283 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4167 G) : Equation4283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose step9 step13
  have step29 (X0 : G) :  ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step12 step9
  have step31 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step14 step29
  have step35 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step14 step31
  have step39 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step35 step11
  have step77 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose step39 step9
  have step83 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step39 step77
  have step228 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step83 step10
  subsumption step228 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation419_implies_Equation436 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation419 G) : Equation436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step31 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step19 step12
  have step35 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step12 step31
  have step57 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step35 step35
  have step144 (X0 : G) :  sK0 ≠ (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := superpose step57 step10
  have step197 : sK0 ≠ sK0 := superpose step9 step144
  subsumption step197 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4270_implies_Equation4590 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4270 G) : Equation4590 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := superpose step12 step18
  have step35 (X0 : G) :  ((sK0 ◇ sK0) ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose step23 step10
  subsumption step35 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4275_implies_Equation4409 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4275 G) : Equation4409 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step9 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose step9 step12
  have step37 (X0 X1 X2 X3 : G) :  (X2 ◇ (X2 ◇ (X3 ◇ X1))) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step13 step13
  have step39 (X0 X1 X2 : G) :  (X2 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step13
  have step55 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose step13 step11
  have step77 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step55
  have step92 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step55 step12
  have step116 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step21 step12
  have step120 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step92 step116
  have step403 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) := superpose step20 step37
  have step431 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step77 step37
  have step838 (X0 X1 X2 : G) :  (X2 ◇ (X2 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step20 step39
  have step915 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step431 step838
  have step928 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step120 step915
  have step929 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step403 step928
  have step1182 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step929 step55
  have step1209 : sK1 ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step929 step10
  have step1210 : sK1 ≠ (sK1 ◇ (sK1 ◇ sK1)) := superpose step9 step1209
  subsumption step1210 step1182


@[equational_result]
theorem Finite.Equation677_and_Equation4283_implies_Equation4358 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4283 G) : Equation4358 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step9 step12
  have step24 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step12 step18
  have step35 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose step24 step10
  subsumption step35 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4290_implies_Equation4408 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4290 G) : Equation4408 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step23
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step26
  have step30 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step27 step11
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step27 step9
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step13 step33
  have step42 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step30 step36
  have step88 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ sK0) := superpose step42 step10
  have step96 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := superpose step42 step9
  subsumption step88 step96


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation332 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation332 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step12
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step25
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step30
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step27 step34
  have step38 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step36 step12
  have step70 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step38 step36
  have step71 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step70
  have step75 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step71
  have step129 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := superpose step75 step10
  subsumption step129 step9


@[equational_result]
theorem Finite.Equation677_and_Equation4358_implies_Equation4398 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4358 G) : Equation4398 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step31 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) := superpose step9 step12
  have step49 (X1 X2 : G) :  (X1 ◇ X2) = (X2 ◇ X1) := superpose step12 step31
  have step64 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step49 step10
  subsumption step64 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation436_implies_Equation500 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation436 G) : Equation500 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := superpose step15 step15
  have step23 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose step15 step12
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step15 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1)) := superpose step15 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step31 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step17 step15
  have step84 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step29 step17
  have step85 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step29 step12
  have step110 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2) = ((X2 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose step20 step16
  have step115 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step16
  have step135 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step16 step115
  have step142 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step31 step135
  have step143 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step84 step142
  have step422 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step85 step16
  have step427 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step12 step422
  have step432 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step84 step427
  have step435 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step15 step432
  have step438 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step84 step435
  have step450 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step84 step23
  have step469 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step23 step15
  have step490 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step24 step469
  have step506 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step84 step450
  have step520 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step18 step490
  have step531 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose step438 step506
  have step540 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step84 step520
  have step542 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step15 step531
  have step548 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step84 step542
  have step560 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step548 step11
  have step588 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step540 step560
  have step606 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step31 step16
  have step611 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step84 step606
  have step622 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step84 step611
  have step631 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step143 step622
  have step640 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step548 step631
  have step649 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step110 step640
  have step655 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose step17 step649
  have step659 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step655
  have step670 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step659 step20
  have step692 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step659 step12
  have step695 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose step659 step10
  have step696 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose step15 step695
  have step699 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step692
  have step716 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose step659 step670
  have step721 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step84 step696
  have step738 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step699 step716
  have step741 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step588 step721
  subsumption step741 step738


@[equational_result]
theorem Finite.Equation677_and_Equation4380_implies_Equation411 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4380 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step21 : sK0 ≠ sK0 := superpose step15 step10
  subsumption step21 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4383_implies_Equation4585 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4383 G) : Equation4585 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step15 : ((sK0 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step10
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation439_implies_Equation510 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation439 G) : Equation510 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step9
  have step20 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step15 step11
  have step24 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step20 step9
  have step31 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step44 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step15 step31
  have step49 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose step24 step44
  have step53 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step24 step49
  have step59 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step24 step10
  subsumption step59 step53


@[equational_result]
theorem Finite.Equation677_and_Equation4398_implies_Equation4482 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4398 G) : Equation4482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step11 step9
  have step41 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose step17 step10
  subsumption step41 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4406_implies_Equation464 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4406 G) : Equation464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step11
  have step39 : sK0 ≠ sK0 := superpose step18 step10
  subsumption step39 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4408_implies_Equation271 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4408 G) : Equation271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step11
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := superpose step9 step12
  have step25 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := superpose step13 step19
  have step63 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step13
  have step64 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step11 step13
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step75 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step25 step66
  have step77 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step64
  have step78 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step63
  have step84 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step75
  have step85 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step77
  have step86 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step17 step78
  have step87 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step84 step85
  have step88 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step84 step86
  have step89 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step84 step87
  have step90 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step84 step88
  have step91 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step84 step89
  have step92 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step84 step91
  have step93 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step90 step92
  have step151 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose step93 step21
  have step153 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose step93 step9
  have step582 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step153 step153
  have step965 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step151 step13
  have step975 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step93 step965
  have step1024 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step93 step975
  have step1059 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step151 step1024
  have step1189 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))))) := superpose step25 step16
  have step1200 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))))) := superpose step93 step1189
  have step1243 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)))) := superpose step93 step1200
  have step1284 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step93 step1243
  have step1320 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step582 step1284
  have step1348 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step582 step1320
  have step1372 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step153 step1348
  have step1389 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step1059 step1372
  have step1401 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step153 step1389
  have step1412 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step582 step1401
  have step1475 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) = X0 := superpose step582 step12
  have step1501 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) = X0 := superpose step582 step1475
  have step3243 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step1412 step20
  have step3266 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step582 step3243
  have step3310 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) := superpose step151 step3266
  have step3346 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose step582 step3310
  have step3373 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose step1501 step3346
  have step3507 : sK0 ≠ sK0 := superpose step3373 step10
  subsumption step3507 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4409_implies_Equation16 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4409 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step14 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step9 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1))) = X1 := superpose step9 step12
  have step25 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose step13 step20
  have step52 (X0 : G) :  sK0 ≠ (X0 ◇ (X0 ◇ sK0)) := superpose step14 step10
  have step87 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step9 step52
  have step155 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step13 step12
  have step170 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step25 step155
  have step184 : sK0 ≠ sK0 := superpose step170 step87
  subsumption step184 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4435_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4435 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step9 step11
  have step46 : sK0 ≠ sK0 := superpose step16 step10
  subsumption step46 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4443_implies_Equation466 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4443 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose step9 step11
  have step42 : sK0 ≠ sK0 := superpose step18 step10
  subsumption step42 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4470_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4470 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) = X1 := superpose step9 step11
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step9 step15
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step34
  have step52 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step9 step17
  have step59 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step39 step52
  have step67 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step59 step17
  have step72 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step59 step9
  have step89 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step9 step67
  have step92 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step72 step89
  have step176 : sK0 ≠ sK0 := superpose step92 step10
  subsumption step176 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4479_implies_Equation4605 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4479 G) : Equation4605 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : ((sK1 ◇ sK0) ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step14 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose step9 step10
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step18 step9
  have step22 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step18 step21
  have step28 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step18 step12
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step28
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step31 step12
  have step52 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step13 step13
  have step58 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step31 step52
  have step65 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step31 step58
  have step68 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step35 step65
  have step77 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose step68 step14
  have step78 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step68 step77
  subsumption step78 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4482_implies_Equation4531 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4482 G) : Equation4531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK1 ◇ sK2) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step22
  have step26 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step9 step20
  have step27 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step25
  have step105 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step27 step12
  have step108 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9 step105
  have step109 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step26 step108
  have step115 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step109 step16
  have step193 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step115 step9
  have step355 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose step193 step10
  subsumption step355 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4531_implies_Equation4544 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4531 G) : Equation4544 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK2 ◇ sK1)) := superpose step9 step10
  have step21 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step11 step9
  have step36 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK0 ◇ (sK1 ◇ sK2)) := superpose step21 step15
  subsumption step36 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4544_implies_Equation4677 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4544 G) : Equation4677 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK1 ◇ sK0) ◇ sK2) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step9 step11
  have step64 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step24 step12
  have step76 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step64
  have step85 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step76
  have step111 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step85 step9
  have step112 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose step9 step111
  have step116 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step85 step112
  have step387 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose step116 step10
  subsumption step387 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4585_implies_Equation26 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4585 G) : Equation26 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step9 step10
  have step15 (X0 : G) :  sK0 ≠ ((sK0 ◇ X0) ◇ X0) := superpose step9 step14
  have step19 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step79 (X0 : G) :  sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ X0) ◇ X0))) := superpose step19 step15
  subsumption step79 step19


@[equational_result]
theorem Finite.Equation677_and_Equation4590_implies_Equation40 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4590 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)))) = X1 := superpose step9 step11
  have step15 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step71 (X0 X1 X2 : G) :  (X2 ◇ X2) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose step13 step17
  have step113 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose step13 step14
  have step124 (X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose step71 step113
  have step134 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step124 step13
  have step162 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)))) := superpose step13 step15
  have step173 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose step134 step162
  have step180 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose step134 step173
  have step182 (X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X2 ◇ X2)) := superpose step134 step180
  have step184 (X1 X2 : G) :  (X1 ◇ X1) = (X2 ◇ X2) := superpose step134 step182
  have step218 (X0 : G) :  (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose step184 step10
  subsumption step218 step184


@[equational_result]
theorem Finite.Equation677_and_Equation4591_implies_Equation623 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4591 G) : Equation623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 : G) :  sK0 ≠ (sK0 ◇ (sK0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step10
  have step26 : sK0 ≠ sK0 := superpose step11 step18
  subsumption step26 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4598_implies_Equation679 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4598 G) : Equation679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step10
  subsumption step14 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4605_implies_Equation384 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4605 G) : Equation384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : ((sK1 ◇ sK0) ◇ sK0) ≠ (sK0 ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose step9 step9
  have step15 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step9 step10
  have step19 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step20 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step43 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose step12 step14
  have step58 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step43
  have step217 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step58 step21
  have step218 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step12 step217
  have step317 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step218 step19
  have step337 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step19 step317
  have step357 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step337 step22
  have step361 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step337 step14
  have step376 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step14 step357
  have step380 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step376
  have step390 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step14 step20
  have step447 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step380 step390
  have step465 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step361 step447
  have step474 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step465
  have step527 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step474 step15
  subsumption step527 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4635_implies_Equation670 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4635 G) : Equation670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step38 : sK0 ≠ sK0 := superpose step22 step10
  subsumption step38 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4636_implies_Equation669 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4636 G) : Equation669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose step9 step11
  have step38 : sK0 ≠ sK0 := superpose step21 step10
  subsumption step38 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation464_implies_Equation4406 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation464 G) : Equation4406 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step32 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step243 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0)) := superpose step32 step14
  have step248 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step14 step243
  have step373 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step248 step11
  subsumption step373 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation466_implies_Equation4443 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation466 G) : Equation4443 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step111 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step20 step14
  have step114 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step14 step111
  have step198 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step114 step11
  subsumption step198 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4677_implies_Equation43 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4677 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X0) ◇ X2) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 X2 X3 : G) :  ((X2 ◇ (X1 ◇ X0)) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose step9 step9
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step23 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2))) := superpose step9 step11
  have step422 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose step16 step23
  have step462 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := superpose step21 step422
  have step584 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step462 step10
  subsumption step584 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation474_implies_Equation4435 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation474 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step62 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose step19 step12
  have step65 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step12 step62
  have step79 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step65 step11
  subsumption step79 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation476_implies_Equation2460 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation476 G) : Equation2460 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ (Y ◇ X)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step120 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose step21 step12
  have step124 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := superpose step21 step11
  have step125 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step12 step120
  have step288 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ X1) := superpose step13 step125
  have step512 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose step288 step124
  subsumption step512 step10


@[equational_result]
theorem Finite.Equation677_and_Equation47_implies_Equation99 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation47 G) : Equation99 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step15 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step16 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step17 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step20 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step15 step10
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step15 step12
  have step24 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step22
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step24 step12
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step15 step33
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step36 step12
  have step51 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step49
  have step61 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step17 step16
  have step74 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step61
  have step83 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step36 step74
  have step86 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step17 step83
  have step89 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step86 step16
  have step93 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step24 step89
  have step94 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step93
  have step95 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step9 step14
  have step147 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step51 step95
  have step156 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step94 step147
  have step164 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step17 step156
  have step167 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step94 step164
  have step171 : sK0 ≠ (sK0 ◇ sK0) := superpose step167 step20
  have step181 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step167 step12
  have step184 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step181
  have step340 : sK0 ≠ sK0 := superpose step184 step171
  subsumption step340 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation500_implies_Equation703 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation500 G) : Equation703 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose step11 step11
  have step26 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose step17 step17
  have step87 (X0 : G) :  sK0 ≠ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step26 step12
  have step94 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose step26 step15
  subsumption step87 step94


@[equational_result]
theorem Finite.Equation677_and_Equation510_implies_Equation2337 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation510 G) : Equation2337 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := mod_symm nh
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step19 step17
  have step27 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step24 step12
  have step42 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step27 step12
  have step87 : sK0 ≠ (sK0 ◇ sK0) := superpose step42 step13
  subsumption step87 step27


@[equational_result]
theorem Finite.Equation677_and_Equation55_implies_Equation72 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation55 G) : Equation72 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step13 step16
  have step25 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step9 step24
  have step32 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step9
  have step36 : sK0 ≠ (sK0 ◇ sK0) := superpose step25 step10
  have step119 : sK0 ≠ sK0 := superpose step32 step36
  subsumption step119 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation617_implies_Equation706 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation617 G) : Equation706 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = X0 := superpose step9 step9
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step13
  have step21 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step29 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose step22 step21
  have step37 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step29 step12
  have step40 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step12 step37
  have step43 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step11 step40
  have step362 : sK0 ≠ sK0 := superpose step43 step10
  subsumption step362 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation622_implies_Equation3662 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation622 G) : Equation3662 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0)) := superpose step11 step9
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X2) ◇ X0)) := superpose step17 step17
  have step30 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step12 step30
  have step41 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step19
  have step46 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose step33 step33
  have step113 (X0 : G) :  (sK0 ◇ sK0) ≠ ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := superpose step46 step10
  have step132 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = ((X2 ◇ X2) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := superpose step46 step17
  have step137 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) := superpose step46 step9
  have step140 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2))) = X1 := superpose step46 step12
  have step141 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)))) = X1 := superpose step46 step11
  have step152 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step18
  have step153 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose step17 step18
  have step165 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step169 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) := superpose step18 step11
  have step175 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose step9 step153
  have step176 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step11 step152
  have step365 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) := superpose step17 step22
  have step391 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) := superpose step9 step365
  have step447 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = (X0 ◇ ((((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0))) := superpose step16 step18
  have step576 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step17 step23
  have step1472 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) ◇ (X0 ◇ X0))) := superpose step391 step18
  have step1479 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step12 step1472
  have step1492 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step19 step1479
  have step1654 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step41 step169
  have step1748 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step137 step1654
  have step1750 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step132 step1748
  have step1751 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step1492 step1750
  have step1752 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step137 step1751
  have step1753 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step141 step1752
  have step1822 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))))) := superpose step17 step175
  have step1851 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))))) := superpose step1753 step1822
  have step1863 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step137 step1851
  have step1869 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step140 step1863
  have step1933 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))))) := superpose step17 step176
  have step2005 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))))) := superpose step576 step1933
  have step2031 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step1753 step2005
  have step2046 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1869 step2031
  have step2053 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step140 step2046
  have step2355 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)))) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose step33 step165
  have step2365 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)))) := superpose step46 step165
  have step2389 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ X0) := superpose step2365 step2355
  have step8703 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)))) = ((X2 ◇ X2) ◇ (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)))) := superpose step447 step46
  have step8728 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = ((X2 ◇ X2) ◇ (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)))) := superpose step2053 step8703
  have step8801 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X2 ◇ X2) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) := superpose step2053 step8728
  have step8842 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose step2053 step8801
  have step8883 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step2053 step8842
  have step8923 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose step2053 step8883
  have step8962 (X0 X1 X2 : G) :  (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose step2053 step8923
  have step16852 (X0 X1 : G) :  (sK0 ◇ sK0) ≠ ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step2389 step113
  subsumption step16852 step8962


@[equational_result]
theorem Finite.Equation677_and_Equation623_implies_Equation4591 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation623 G) : Equation4591 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : ((sK1 ◇ sK1) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X0)) := superpose step16 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step27
  have step71 (X0 : G) :  ((X0 ◇ X0) ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step29 step10
  subsumption step71 step29


@[equational_result]
theorem Finite.Equation677_and_Equation639_implies_Equation906 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation639 G) : Equation906 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step13
  have step15 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step14 step15
  have step19 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step9 step18
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step23
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step19 step26
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step29 step9
  have step33 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step29 step12
  have step36 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step21 step33
  have step37 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step32 step36
  have step58 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose step37 step10
  subsumption step58 step19


@[equational_result]
theorem Finite.Equation677_and_Equation669_implies_Equation4636 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation669 G) : Equation4636 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK1) := mod_symm nh
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step102 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step19 step14
  have step107 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step14 step102
  have step142 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose step107 step11
  subsumption step142 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation670_implies_Equation4635 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation670 G) : Equation4635 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) := superpose step19 step12
  have step45 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step42
  have step61 : ((sK0 ◇ sK1) ◇ sK0) ≠ ((sK0 ◇ sK1) ◇ sK0) := superpose step45 step11
  subsumption step61 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation679_implies_Equation4598 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation679 G) : Equation4598 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step51 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose step19 step12
  have step53 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step12 step51
  have step71 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step53 step11
  subsumption step71 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation703_implies_Equation833 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation703 G) : Equation833 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((s ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step16
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step22 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step11 step16
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step16 step14
  have step28 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step14 step16
  have step34 (X0 X1 X2 : G) :  (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := superpose step13 step11
  have step74 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose step34 step11
  have step81 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose step34 step16
  have step148 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step11 step22
  have step185 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step11 step148
  have step193 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step28 step185
  have step196 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step193
  have step201 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step196 step16
  have step249 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step201 step196
  have step275 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step74 step27
  have step359 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step20 step275
  have step389 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step81 step359
  have step401 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step249 step389
  have step425 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose step401 step22
  have step456 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step401 step425
  have step3152 : sK0 ≠ (sK0 ◇ sK0) := superpose step456 step12
  subsumption step3152 step401


@[equational_result]
theorem Finite.Equation677_and_Equation706_implies_Equation826 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation706 G) : Equation826 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = X1 := superpose step14 step15
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step23 step14
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step23 step11
  have step35 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step31 step29
  have step57 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step35 step12
  have step58 : sK0 ≠ (sK0 ◇ sK0) := superpose step23 step57
  subsumption step58 step35


@[equational_result]
theorem Finite.Equation677_and_Equation707_implies_Equation1316 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation707 G) : Equation1316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step16 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step13 step16


@[equational_result]
theorem Finite.Equation677_and_Equation72_implies_Equation118 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation72 G) : Equation118 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ s))) := by
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
  have step17 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step11
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step17 step15
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step14 step24
  have step35 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step13 step17
  have step41 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step13 step27
  have step43 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step17
  have step53 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step35 step41
  have step66 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step14
  have step67 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step43 step66
  have step77 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step53 step67
  have step184 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step77 step12
  subsumption step184 step53


@[equational_result]
theorem Finite.Equation677_and_Equation75_implies_Equation439 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation75 G) : Equation439 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step10
  have step16 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step9
  have step17 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step16 step9
  have step25 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose step9 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step12 step9
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step17
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step17 step9
  have step51 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step16 step25
  have step78 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step9
  have step79 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step28 step78
  have step220 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step42
  have step259 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step16 step220
  have step268 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step28 step259
  have step274 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step79 step268
  have step344 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step79 step11
  have step362 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step51 step344
  have step378 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step37 step42
  have step379 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step37 step378
  have step389 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step379
  have step399 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step389 step17
  have step402 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step389 step27
  have step404 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step389 step42
  have step405 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step16 step404
  have step407 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step16 step402
  have step410 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step21 step399
  have step416 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step37 step405
  have step418 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step274 step407
  have step421 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step16 step410
  have step427 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step21 step416
  have step429 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step362 step418
  have step434 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step421 step427
  have step435 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step16 step429
  have step437 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step434 step435
  have step504 : sK0 ≠ sK0 := superpose step437 step13
  subsumption step504 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation8_implies_Equation23 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation8 G) : Equation23 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step17 step9
  have step22 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step11
  have step23 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step22
  have step25 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step20 step23
  have step26 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step17 step25
  have step44 : sK0 ≠ (sK0 ◇ sK0) := superpose step26 step10
  subsumption step44 step26


@[equational_result]
theorem Finite.Equation677_and_Equation825_implies_Equation1451 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation825 G) : Equation1451 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step9 step9
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step33 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step12
  have step34 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step12
  have step38 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step34 step33
  have step41 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step21 step38
  have step127 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step41 step12
  have step155 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose step19 step20
  have step190 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose step127 step155
  have step194 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step190
  have step213 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := superpose step194 step10
  have step214 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose step19 step213
  have step230 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step194 step214
  have step238 : sK0 ≠ (sK0 ◇ sK0) := superpose step194 step230
  subsumption step238 step194


@[equational_result]
theorem Finite.Equation677_and_Equation826_implies_Equation1029 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation826 G) : Equation1029 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))))) = X0 := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step12 step17
  have step29 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X2) ◇ (X2 ◇ X2)) := superpose step17 step17
  have step34 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose step17 step9
  have step36 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step17 step12
  have step39 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step36
  have step147 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X0 := superpose step9 step34
  have step168 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step39 step147
  have step188 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step29 step13
  have step219 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step168 step18
  have step222 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step219
  have step313 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step18 step188
  have step417 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step313 step9
  have step437 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step24 step417
  have step444 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step39 step437
  have step449 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step222 step444
  have step537 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose step449 step17
  have step540 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step449 step11
  have step565 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := superpose step540 step537
  have step773 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step540 step10
  have step774 : sK0 ≠ (sK0 ◇ sK0) := superpose step565 step773
  subsumption step774 step540


@[equational_result]
theorem Finite.Equation677_and_Equation833_implies_Equation845 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation833 G) : Equation845 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step33 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step48 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step17 step12
  have step55 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step12 step19
  have step58 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step19
  have step60 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step19 step19
  have step61 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (X1 ◇ X2)) := superpose step19 step19
  have step76 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1)) := superpose step19 step12
  have step80 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step76
  have step81 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step60
  have step119 (X0 X1 X2 : G) :  ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) = (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) := superpose step9 step61
  have step186 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step20
  have step188 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1)) ◇ X0)) := superpose step17 step20
  have step224 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step17 step188
  have step231 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step11 step80
  have step234 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step19 step80
  have step240 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step80 step80
  have step260 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step80
  have step273 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step80 step19
  have step281 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step55 step273
  have step283 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step260
  have step292 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step240
  have step295 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step281 step292
  have step297 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step295
  have step304 (X0 X1 : G) :  (X0 ◇ (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0)) = (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0)) ◇ (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)))) := superpose step14 step15
  have step305 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step19 step15
  have step311 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step80 step15
  have step379 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step311
  have step385 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := superpose step234 step305
  have step386 (X0 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step33 step304
  have step398 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step281 step379
  have step401 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose step58 step385
  have step402 (X0 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step231 step386
  have step410 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step297 step398
  have step412 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := superpose step283 step401
  have step413 (X0 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step186 step402
  have step416 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step412 step413
  have step422 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose step19 step416
  have step963 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step422 step13
  have step1082 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)))) := superpose step15 step33
  have step1091 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) = (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step19 step33
  have step1211 (X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step412 step1091
  have step1220 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose step58 step1082
  have step1246 (X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose step58 step1211
  have step1254 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) ◇ X1)) := superpose step55 step1220
  have step1266 (X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step283 step1246
  have step1271 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step410 step1254
  have step1284 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step119 step1271
  have step1289 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step422 step1284
  have step1290 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step80 step1289
  have step1291 (X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step412 step1290
  have step1292 (X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step1266 step1291
  have step2554 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose step80 step81
  have step2703 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step119 step2554
  have step2757 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step422 step2703
  have step2791 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step963 step2757
  have step2812 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step2791
  have step2842 (X0 X1 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step2812 step48
  have step2844 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step2812 step21
  have step3015 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step224 step14
  have step3020 (X0 X1 : G) :  ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step224 step16
  have step3073 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step2842 step3020
  have step3078 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step2842 step3015
  have step3150 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step12 step3073
  have step3155 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step1292 step3078
  have step3203 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step2812 step3150
  have step3208 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step2844 step3155
  have step3245 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step2844 step3208
  have step3273 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step3203 step3245
  have step3361 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose step3273 step61
  have step3368 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step3273 step10
  have step3373 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step3273 step3361
  have step7480 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step3373 step12
  have step7493 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step3373 step20
  have step7585 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step12 step7493
  have step10955 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step20 step7585
  have step11085 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step7480 step10955
  have step11162 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step7585 step11085
  have step12534 : sK0 ≠ (sK0 ◇ sK0) := superpose step11162 step3368
  subsumption step12534 step3273


@[equational_result]
theorem Finite.Equation677_and_Equation845_implies_Equation883 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation845 G) : Equation883 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step20
  have step29 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X2 ◇ X2) ◇ (X2 ◇ X1)) := superpose step20 step20
  have step36 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X1)) := superpose step20 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step9 step36
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step27
  have step108 (X0 X1 X2 : G) :  (X2 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2))) := superpose step29 step12
  have step110 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X2 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step29 step9
  have step111 (X0 X1 X2 : G) :  (X2 ◇ X1) = ((X2 ◇ X1) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step20 step110
  have step137 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step20 step21
  have step159 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step13 step137
  have step162 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step9 step159
  have step240 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step13 step21
  have step251 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step162 step240
  have step263 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step251
  have step266 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step263
  have step269 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step42 step266
  have step272 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step42 step269
  have step281 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step20 step39
  have step353 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step20 step16
  have step402 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose step281 step353
  have step416 (X0 X1 : G) :  (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose step272 step402
  have step466 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step416 step21
  have step473 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step108 step466
  have step504 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step39 step473
  have step557 (X0 X1 : G) :  (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step20 step17
  have step585 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step21 step557
  have step602 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step504 step585
  have step613 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step504 step602
  have step621 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step20 step613
  have step628 (X1 : G) :  (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose step111 step621
  have step633 (X1 : G) :  (X1 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose step504 step628
  have step646 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step633 step12
  have step663 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step646
  have step766 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step663 step13
  have step777 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose step663 step39
  have step803 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step663 step10
  have step819 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step663 step777
  have step830 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) := superpose step663 step766
  have step839 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose step663 step819
  have step841 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose step663 step830
  have step843 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step839 step841
  have step894 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step19 step12
  have step915 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step504 step894
  have step962 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step633 step915
  have step1007 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose step663 step962
  have step1044 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step663 step1007
  have step1277 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step843 step21
  have step1309 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step1044 step1277
  have step4759 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step1309 step803
  subsumption step4759 step843


@[equational_result]
theorem Finite.Equation677_and_Equation883_implies_Equation916 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation883 G) : Equation916 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step28 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose step13 step15
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step11 step15
  have step31 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step33 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step31 step30
  have step46 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step33 step15
  have step90 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose step46 step14
  have step96 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := superpose step46 step12
  have step97 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step46 step96
  have step133 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step46 step28
  have step193 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose step90 step28
  have step195 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose step133 step193
  have step210 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step46 step195
  have step415 : sK0 ≠ sK0 := superpose step210 step97
  subsumption step415 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation906_implies_Equation1023 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation906 G) : Equation1023 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ ((Y ◇ X) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ (s ◇ s))) := by
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
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step10 step10
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step18 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) := superpose step13 step10
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step14 step13
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step13 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step12
  have step36 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step13 step19
  have step37 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step12 step19
  have step39 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose step19 step19
  have step42 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step19 step12
  have step45 (X0 X1 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X0))) := superpose step19 step14
  have step57 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step39
  have step58 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step19 step37
  have step198 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step26
  have step205 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) := superpose step26 step19
  have step210 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose step19 step205
  have step213 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step19 step198
  have step223 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step57 step213
  have step226 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step21 step223
  have step276 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step16
  have step301 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step276
  have step322 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step45 step301
  have step335 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step322 step26
  have step358 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step19 step335
  have step367 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step14 step358
  have step506 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step24 step19
  have step508 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step24 step26
  have step511 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step508
  have step513 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))))) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step57 step506
  have step525 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step511
  have step526 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step21 step513
  have step536 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step367 step526
  have step550 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step19 step525
  have step562 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step525 step26
  have step563 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step525 step27
  have step570 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step525 step27
  have step577 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step570 step563
  have step578 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step57 step562
  have step585 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step550
  have step587 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step577
  have step588 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step578
  have step594 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step525 step585
  have step596 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step587 step588
  have step600 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step594 step596
  have step620 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step22
  have step658 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step594 step620
  have step672 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step570 step658
  have step676 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step13 step672
  have step679 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step600 step676
  have step756 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))))) := superpose step24 step15
  have step760 (X0 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))))) := superpose step42 step15
  have step767 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step525 step15
  have step826 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step19 step767
  have step833 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step24 step760
  have step837 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))))) := superpose step19 step756
  have step860 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step58 step826
  have step865 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step19 step833
  have step869 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))))) := superpose step58 step837
  have step878 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step13 step860
  have step882 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step226 step865
  have step883 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) := superpose step13 step869
  have step888 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step57 step878
  have step891 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step594 step882
  have step892 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) := superpose step57 step883
  have step896 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step21 step888
  have step899 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step42 step891
  have step900 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) := superpose step21 step892
  have step903 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step536 step896
  have step905 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) := superpose step536 step900
  have step907 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step899 step903
  have step908 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step899 step905
  have step910 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step899 step907
  have step911 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step908
  have step912 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step679 step911
  have step913 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step910 step912
  have step920 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose step913 step12
  have step937 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step913 step10
  have step940 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose step913 step19
  have step997 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))))) := superpose step26 step18
  have step1016 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step18 step14
  have step1037 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step36 step1016
  have step1052 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) := superpose step913 step997
  have step1077 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose step940 step1037
  have step1091 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))))) := superpose step210 step1052
  have step1113 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step940 step1077
  have step1121 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1))) := superpose step937 step1091
  have step1138 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step937 step1113
  have step1145 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step913 step1121
  have step1156 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step913 step1145
  have step1687 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) := superpose step26 step937
  have step1746 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose step913 step1687
  have step1773 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step913 step1746
  have step2883 (X0 X1 : G) :  (X0 ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step1138 step920
  have step3897 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step1156 step20
  have step3919 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step940 step3897
  have step3983 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step1773 step3919
  have step4030 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step2883 step3983
  have step4771 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step4030 step920
  have step4782 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step920 step4771
  have step5351 : sK0 ≠ (sK0 ◇ sK0) := superpose step4782 step11
  subsumption step5351 step913


@[equational_result]
theorem Finite.Equation677_and_Equation916_implies_Equation1039 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation916 G) : Equation1039 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ ((Y ◇ Y) ◇ X)) ◇ (Y ◇ ((Y ◇ Y) ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ Y) ◇ ((Y ◇ X) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ Y) ◇ (s ◇ s))) := by
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
  have step20 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step15
  have step21 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step20 step15
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step28
  have step32 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step14 step16
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step29 step20
  have step69 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step13 step29
  have step70 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose step13 step20
  have step83 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose step48 step70
  have step84 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose step48 step69
  have step95 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step83 step84
  have step151 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step16 step95
  have step160 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step95 step16
  have step170 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step95 step151
  have step916 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step16 step21
  have step1042 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step48 step916
  have step1107 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose step95 step1042
  have step1149 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step48 step1107
  have step1169 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step160 step1149
  have step1180 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step21 step170
  have step1193 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step170 step170
  have step1237 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step1193 step1180
  have step1249 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step48 step1237
  have step1252 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step48 step1249
  have step1254 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step1169 step1252
  have step1985 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step32 step95
  have step2003 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose step48 step1985
  have step2065 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step1193 step2003
  have step2111 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose step48 step2065
  have step4328 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := superpose step2111 step12
  have step4329 : sK0 ≠ (sK0 ◇ sK0) := superpose step1254 step4328
  subsumption step4329 step48


@[equational_result]
theorem Finite.Equation677_and_Equation99_implies_Equation151 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation99 G) : Equation151 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step11
  have step28 : sK0 ≠ (sK0 ◇ sK0) := superpose step15 step10
  subsumption step28 step15


