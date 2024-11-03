
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[0,0,2],[1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[0,0,2],[1,1,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[0,0,2],[1,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[0,0,2],[1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3755] [3268, 3271, 3278, 3281, 3343, 3346, 3353, 3474, 3481, 3484, 3546, 3549, 3556, 3664, 3667, 3684, 3687, 3722, 3725, 3759, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4121, 4131, 4158, 4272, 4275, 4291, 4320, 4399, 4435, 4445, 4473, 4599, 4622, 4631, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[0,0,2],[1,1,2]]», Finite.of_fintype _, by decideFin!⟩
