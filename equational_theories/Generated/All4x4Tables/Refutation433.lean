import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3884,3888,3894,3898,3910] [359,360,361,365,367,368,369,371,378,3253,3255,3256,3278,3279,3282,3285,3286,3306,3315,3316,3318,3319,3321,3322,3323,3721,3724,3725,3726,3727,3729,3865,3887,3895,3915,3925,3928,3931,3935,3943,4065,4066,4067,4068,4069,4070,4071,4072,4073,4076,4081,4083,4084,4085,4087,4090,4091,4092,4093,4094,4095,4096,4097,4098,4099,4101,4104,4105,4106,4107,4109,4113,4131,4269,4293,4314,4316,4318,4583,4584,4588,4591,4592,4594,4597,4598,4601,4606,4608,4609,4611,4616,4620,4623,4626,4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]», by decideFin!⟩
