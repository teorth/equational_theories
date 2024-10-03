import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [224,2293,2296,2306,2310,2322,2333,2376,2665,2699,2702,2739,2778,2782] [31,231,242,246,309,312,1637,1657,1672,1718,1721,1724,1731,1746,2340,2351,2355,2385,2389,2402,2406,2420,2425,2430,2496,2506,2517,2533,2536,2543,2554,2558,2571,2588,2605,2623,2652,2672,2687,2706,2709,2712,2724,2746,2761,2791,2795,2812,2836,3058,3078,3093,3105,3115,3139,3142,3145,3152,3167,3180,3197,3255,3258,3261,3264,3268,3271,3274,3278,3288,3467,3481,3509,3529,3537,3677,3694,3820,4090,4131,4155,4165,4175,4226,4269,4272,4316,4327,4351,4362,4590,4606,4611,4622] :=
    ⟨Fin 4, «FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]», by decideFin!⟩
