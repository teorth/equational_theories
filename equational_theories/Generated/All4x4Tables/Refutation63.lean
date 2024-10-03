import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3714,3721,3724,3748,3749,3751,3752,3759,3761,4291,4293,4321,4399,4406,4436,4443,4629,4636,4658] [307,323,325,326,332,333,335,359,375,377,378,384,385,387,3253,3306,3308,3309,3315,3316,3318,3319,3342,3343,3345,3346,3352,3353,3355,3456,3509,3511,3512,3518,3519,3521,3522,3545,3546,3548,3549,3555,3556,3558,3715,3758,3862,3915,3917,3918,3924,3925,3928,3951,3952,3955,3962,3964,4065,4118,4121,4127,4128,4131,4154,4155,4158,4165,4167,4284,4290,4314,4320,4343,4362,4369,4396,4433,4470,4480,4512,4515,4598,4599,4605,4606,4608,4673,4679,4684] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[3,0,3,3],[0,3,0,3],[3,3,3,3]]», by decideFin!⟩
