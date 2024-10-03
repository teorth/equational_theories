import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2588,2812] [211,218,246,307,312,2238,2246,2253,2263,2266,2281,2290,2303,2318,2327,2340,2355,2364,2385,2406,2430,2662,2706,2733,2761,2795,3058,3139,3152,3167,3458,3464,3509,3522,3537,3659,3684,3712,3759,3820,4090,4118,4165,4226,4590,4622] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]», by decideFin!⟩
