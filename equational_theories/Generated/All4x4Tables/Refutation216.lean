import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,1],[3,1,1,1],[2,3,3,3],[2,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,1],[3,1,1,1],[2,3,3,3],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,1],[3,1,1,1],[2,3,3,3],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,1],[3,1,1,1],[2,3,3,3],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3873,3918,3921,3931,3939,3943,3947,4271,4285,4286,4287,4289,4315,4317,4319,4339,4340,4342,4357,4359,4360,4361] [307,308,309,310,311,359,360,361,375,378,381,3253,3254,3255,3256,3257,3258,3259,3260,3261,3262,3263,3264,3265,3266,3267,3306,3309,3312,3315,3316,3318,3319,3321,3322,3323,3326,3330,3334,3338,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466,3467,3468,3469,3470,4065,4067,4070,4073,4076,4118,4121,4124,4128,4131,4134,4138,4142,4146,4150,4584,4599,4602,4605,4608,4610,4631,4655,4658,4660,4675,4684,4686] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,1],[3,1,1,1],[2,3,3,3],[2,3,3,3]]», by decideFin!⟩
