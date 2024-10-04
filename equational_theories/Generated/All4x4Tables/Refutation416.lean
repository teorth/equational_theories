import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,0,3],[2,3,3,3],[2,2,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,0,3],[2,3,3,3],[2,2,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,0,3],[2,3,3,3],[2,2,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,0,3],[2,3,3,3],[2,2,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [308,310,312,315,316,317,320,3254,3257,3263,3270,3275,3289,3296,3297,3299,3301,4304] [309,311,313,314,318,319,321,359,360,367,368,369,378,3259,3260,3265,3271,3273,3274,3290,3292,3294,3295,3302,3306,3456,3457,3458,3459,3464,3472,3481,3482,3484,3485,3488,3489,3500,3509,3522,3537,3667,3675,3687,3703,3712,3749,3759,3820,3862,3864,3867,3870,3873,3877,3880,3883,3887,3890,3893,3897,3901,3905,3909,4065,4068,4090,4094,4098,4118,4131,4165,4226,4269,4273,4278,4287,4291,4296,4300,4310,4316,4320,4321,4323,4325,4327,4330,4332,4334,4340,4348,4354,4360,4362,4367,4374,4378,4599] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,0,3],[2,3,3,3],[2,2,3,3]]», by decideFin!⟩
