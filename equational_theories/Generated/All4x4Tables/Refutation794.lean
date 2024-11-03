
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3342, 3964] [3306, 3308, 3315, 3319, 3346, 3353, 3509, 3511, 3518, 3545, 3549, 3556, 3558, 3659, 3915, 3917, 3924, 3928, 3951, 3955, 3962, 4120, 4127, 4131, 4158, 4165, 4167, 4283, 4290, 4320, 4380, 4598, 4605, 4635] :=
    ⟨Fin 6, «FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]», Finite.of_fintype _, by decideFin!⟩
