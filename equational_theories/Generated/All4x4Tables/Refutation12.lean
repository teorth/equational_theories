
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [329, 395, 3798, 4559] [3268, 3271, 3278, 3281, 3343, 3346, 3353, 3474, 3481, 3484, 3546, 3549, 3556, 3587, 3591, 3600, 3617, 3664, 3667, 3684, 3687, 3722, 3725, 3759, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4096, 4104, 4121, 4131, 4158, 4272, 4275, 4291, 4320, 4399, 4435, 4445, 4473, 4599, 4611, 4619, 4622, 4631, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]]», by decideFin!⟩
