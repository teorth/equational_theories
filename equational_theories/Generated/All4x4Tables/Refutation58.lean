
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[1,2,1],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,2],[1,2,1],[2,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[1,2,1],[2,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,2],[1,2,1],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [427, 823, 1023, 1038, 1229, 1231, 1850, 1861, 4068] [820, 1028, 1035, 1039, 1045, 1046, 1225, 1228, 1239, 1241, 1249, 1834, 1847, 1851, 1857, 1860, 3255, 3256, 3316, 3318, 3659, 3864, 3865, 3867, 3870, 3887, 3925, 3928, 4066, 4067, 4070, 4071, 4269, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 3, «All4x4Tables [[0,0,2],[1,2,1],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
