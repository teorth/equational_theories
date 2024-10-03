import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2296,2330,2340,2351,2406] [23,25,31,208,211,214,218,221,224,242,246,307,309,312,323,1629,1631,1637,1644,1647,1650,1657,1672,1718,1721,1724,1731,1746,2253,2256,2259,2263,2273,2277,2281,2300,2303,2310,2314,2318,2327,2355,2364,2368,2372,2385,2389,2425,2430,2441,2443,2446,2449,2456,2466,2476,2496,2506,2517,2530,2533,2543,2554,2571,2588,2605,2623,2646,2659,2696,2733,2770,3065,3253,3461,3519,3522,3659,3674,3749,3759,4065,4070,4118,4320] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,0,0,3],[1,3,3,3],[0,1,2,3]]», by decideFin!⟩
