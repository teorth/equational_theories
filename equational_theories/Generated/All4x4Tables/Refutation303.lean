import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [221,2253,2256,2266,2277,2281,2290,2293,2303,2314,2318,2330,2368,2372] [23,25,31,205,208,214,218,231,246,307,312,1629,1637,1718,1731,1746,2240,2249,2259,2263,2327,2340,2351,2355,2364,2385,2406,2430,2441,2446,2449,2456,2459,2466,2469,2496,2506,2530,2533,2543,2554,2605,2644,2652,2659,2662,2672,2687,2696,2706,2709,2724,2733,2736,2746,2761,2770,2791,2795,2812,2836,3050,3058,3065,3139,3152,3167,3253,3258,3268,3278,3288,3458,3522,3537,3664,3674,3677,3694,3749,3759,3820,4065,4090,4118,4165,4226,4272,4351,4590,4622] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,3,1,3],[3,0,0,3],[0,1,2,3]]», by decideFin!⟩
