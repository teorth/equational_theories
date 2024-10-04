import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [372,3469,3479,3483,3486,3487,3490,3499,3501,3502,3506,3671,3679,3696,3698,3701,3708,3872,3875,3879,3885,3890,3892,3905,3907,3908,3912,4075,4078,4081,4082,4088,4108,4111,4115] [3462,3463,3467,3468,3470,3474,3476,3477,3478,3480,3492,3493,3494,3495,3497,3498,3503,3504,3505,3507,3667,3669,3670,3675,3676,3702,3703,3705,3864,3866,3868,3869,3873,3874,3876,3880,3882,3883,3884,3886,3888,3889,3893,3894,3896,3898,3899,3900,3901,3903,3904,3909,3910,3911,3913,4071,4072,4076,4077,4083,4086,4102,4104,4106,4114,4268,4269,4282,4284,4288,4314,4316,4318,4584,4606,4611,4631,4635,4684] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,2,3],[0,3,3,3],[3,3,3,3]]», by decideFin!⟩
