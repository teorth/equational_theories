
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,1,4,3,0,2],[3,2,1,2,4,5],[4,3,4,1,2,0],[1,2,3,2,5,4],[2,5,0,4,3,3],[0,4,2,5,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,1,4,3,0,2],[3,2,1,2,4,5],[4,3,4,1,2,0],[1,2,3,2,5,4],[2,5,0,4,3,3],[0,4,2,5,3,3]]» : Magma (Fin 6) where
  op := finOpTable "[[4,1,4,3,0,2],[3,2,1,2,4,5],[4,3,4,1,2,0],[1,2,3,2,5,4],[2,5,0,4,3,3],[0,4,2,5,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,1,4,3,0,2],[3,2,1,2,4,5],[4,3,4,1,2,0],[1,2,3,2,5,4],[2,5,0,4,3,3],[0,4,2,5,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3545, 4167] [3306, 3308, 3315, 3342, 3346, 3353, 3509, 3511, 3518, 3522, 3549, 3556, 3558, 3659, 3917, 3924, 3928, 3951, 3955, 3962, 3964, 4118, 4120, 4127, 4131, 4158, 4165, 4283, 4290, 4320, 4380, 4598, 4605, 4635] :=
    ⟨Fin 6, «All4x4Tables [[4,1,4,3,0,2],[3,2,1,2,4,5],[4,3,4,1,2,0],[1,2,3,2,5,4],[2,5,0,4,3,3],[0,4,2,5,3,3]]», Finite.of_fintype _, by decideFin!⟩
