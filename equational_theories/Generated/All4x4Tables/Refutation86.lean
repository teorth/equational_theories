import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[3,3,1,0],[3,0,2,1],[1,0,3,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[3,3,1,0],[3,0,2,1],[1,0,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[3,3,1,0],[3,0,2,1],[1,0,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[3,3,1,0],[3,0,2,1],[1,0,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3355] [43,307,323,325,326,332,333,335,359,375,377,378,384,385,387,3306,3308,3309,3315,3316,3318,3319,3342,3343,3345,3346,3352,3353,3509,3511,3512,3518,3519,3521,3522,3545,3546,3548,3549,3555,3556,3558,3659,3712,3714,3715,3721,3722,3724,3725,3748,3749,3751,3752,3758,3759,3761,3915,3917,3918,3924,3925,3927,3928,3951,3952,3954,3955,3961,3962,3964,4118,4120,4121,4127,4128,4130,4154,4157,4167,4284,4290,4291,4293,4343,4358,4364,4369,4396,4398,4399,4405,4406,4408,4433,4436,4442,4445,4470,4472,4473,4480,4482,4512,4515,4525,4531,4541,4544,4599,4608,4629,4658,4677,4679] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[3,3,1,0],[3,0,2,1],[1,0,3,0]]», by decideFin!⟩
