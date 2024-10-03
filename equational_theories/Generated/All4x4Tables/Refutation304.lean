import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2517,2672,2687] [203,208,211,218,221,231,242,246,307,309,310,312,323,2238,2243,2246,2253,2256,2263,2266,2273,2277,2281,2290,2293,2300,2303,2310,2314,2318,2327,2330,2340,2351,2355,2364,2368,2372,2385,2389,2402,2406,2420,2425,2430,2449,2456,2476,2533,2554,2571,2588,2623,2646,2665,2696,2709,2724,2770,2791,2812,2836,3253,3255,3256,3258,3259,3261,3262,3264,3265,3266,3268,3271,3274,3278,3288,3306,3458,3461,3467,3519,3664,3674,3694,3749,4272,4314,4351,4584,4631] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,1,3],[0,3,3,0],[0,1,2,3]]», by decideFin!⟩
