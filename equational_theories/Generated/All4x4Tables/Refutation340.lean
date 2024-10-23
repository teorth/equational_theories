
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4154] [3308, 3315, 3319, 3342, 3346, 3353, 3355, 3509, 3511, 3518, 3522, 3545, 3549, 3556, 3558, 3659, 3915, 3917, 3924, 3928, 3951, 3955, 3962, 3964, 4118, 4120, 4127, 4158, 4165, 4167, 4283, 4290, 4320, 4396, 4398, 4405, 4433, 4442, 4473, 4480, 4482, 4598, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]», Finite.of_fintype _, by decideFin!⟩
