import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[2,3,2,3],[2,2,2,3],[3,2,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[2,3,2,3],[2,2,2,3],[3,2,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[2,3,2,3],[2,2,2,3],[3,2,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[2,3,2,3],[2,2,2,3],[3,2,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [333,343,3343,3363,3380,3397,3414,3431,3732,3769,3786,3803,3820,3837,4300,4330,4374] [359,375,378,385,3319,3456,3471,3512,3519,3549,3556,3587,3600,3862,3864,3867,3870,3873,3877,3915,3918,3925,3955,3962,3993,4006,4065,4118,4128,4131,4155,4158,4380,4399,4406,4435,4442,4483,4533,4546,4635] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[2,3,2,3],[2,2,2,3],[3,2,2,3]]», by decideFin!⟩
