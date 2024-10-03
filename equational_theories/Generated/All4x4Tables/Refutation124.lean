import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2351,2385,2406] [23,25,31,205,208,211,214,218,221,224,242,246,307,309,312,323,1629,1631,1637,1644,1647,1650,1657,1672,1718,1721,1724,1731,1746,2240,2246,2263,2281,2318,2327,2355,2364,2430,2446,2466,2496,2506,2530,2533,2543,2554,2605,2644,2652,2659,2662,2672,2687,2696,2706,2709,2724,2733,2746,2761,2770,2791,2795,2812,2836,3050,3058,3139,3152,3167,3253,3255,3258,3261,3264,3268,3271,3274,3278,3288,3456,3458,3464,3467,3509,3522,3537,3659,3664,3674,3677,3684,3694,3712,3749,3759,3820,4090,4118,4131,4165,4226,4269,4272,4316,4327,4351,4590,4622] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]», by decideFin!⟩
