import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3475,3478,3482,3485,3488,3492,3496,3500,3504,3680] [307,309,310,312,313,316,319,320,323,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3268,3269,3271,3272,3274,3275,3276,3278,3279,3282,3285,3286,3288,3289,3290,3293,3294,3297,3298,3301,3302,3303,3306,3459,3481,3489,3509,3519,3522,3525,3529,3537,3712,3749,3759,3769,3786,3820,4065,4068,4070,4084,4090,4094,4098,4105,4118,4128,4131,4138,4155,4165,4175,4226,4269,4272,4273,4276,4279,4280,4314,4316,4318,4320,4325,4332,4343,4346,4351,4355,4362,4584,4606,4611,4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,3,3],[2,3,3,3]]», by decideFin!⟩
