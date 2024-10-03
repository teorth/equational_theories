import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3515,3519,3522,3525,3529,3533,3537,3541] [307,309,310,323,325,326,329,359,361,375,377,378,381,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3306,3308,3309,3312,3315,3316,3318,3319,3322,3326,3330,3334,3338,3459,3511,3661,3664,3667,3670,3712,3715,3718,3722,3725,3728,3732,3736,3740,3744,3862,3864,3867,3870,3873,3915,3918,3921,3925,3928,3931,3935,3939,3943,3947,4065,4067,4070,4073,4076,4118,4121,4124,4128,4131,4134,4138,4142,4146,4150,4269,4284,4287,4316,4340,4360,4380,4382,4396,4399,4402,4432,4435,4438,4470,4473,4476,4508,4512,4516,4520,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[2,3,2,3],[2,1,2,1],[2,3,2,3]]», by decideFin!⟩
