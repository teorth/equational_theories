import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [4154] [43,307,323,325,326,332,333,335,359,375,377,378,384,385,387,3309,3319,3342,3345,3346,3353,3355,3509,3512,3522,3545,3546,3548,3549,3555,3556,3659,3712,3714,3715,3721,3722,3724,3725,3748,3749,3751,3752,3758,3759,3915,3917,3918,3927,3928,3951,3961,3964,4118,4120,4121,4130,4158,4164,4167,4283,4284,4291,4293,4343,4358,4364,4396,4398,4399,4405,4406,4433,4436,4442,4445,4470,4472,4473,4479,4480,4482,4512,4515,4525,4531,4541,4544,4599,4605,4608,4629,4635,4658,4677,4679,4684] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,3,3,2],[3,3,1,1],[1,2,1,2]]», by decideFin!⟩
