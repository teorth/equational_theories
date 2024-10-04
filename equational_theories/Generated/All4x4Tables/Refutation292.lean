import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2303] [203,211,214,221,224,231,242,246,309,312,323,1631,1637,1644,1647,1650,1657,1672,1718,1721,1724,1731,1746,2240,2243,2246,2249,2253,2266,2281,2290,2318,2340,2355,2364,2385,2406,2430,2446,2466,2496,2506,2533,2543,2554,2605,2652,2672,2687,2709,2724,2746,2761,2791,2795,2812,2836,3058,3152,3167,3258,3268,3278,3288,3458,3464,3509,3537,3659,3664,3674,3677,3684,3694,3712,3749,3759,3820,4090,4165,4226,4272,4351,4590,4622] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]», by decideFin!⟩
