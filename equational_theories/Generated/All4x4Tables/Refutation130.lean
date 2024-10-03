import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2300,2706,2712,2774,3180] [31,221,224,231,242,246,312,1637,1657,1672,1718,1721,1724,1731,1746,2293,2296,2314,2318,2322,2330,2333,2340,2351,2355,2364,2368,2372,2376,2385,2389,2402,2406,2420,2425,2430,2496,2506,2517,2533,2536,2543,2554,2558,2571,2588,2605,2623,2652,2662,2665,2672,2687,2724,2739,2746,2761,2778,2782,2791,2795,2812,2836,3058,3093,3115,3139,3145,3152,3167,3197,3258,3268,3278,3288,3509,3529,3537,3659,3664,3674,3677,3684,3694,3712,3749,3759,3769,3786,3820,4090,4155,4175,4226,4272,4320,4327,4351,4362,4590,4606,4611,4622] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]», by decideFin!⟩
