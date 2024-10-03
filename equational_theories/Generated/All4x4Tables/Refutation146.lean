import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [31,218,242,246,309,319,2310,2351,2355,2364,2389,2402,2420,2425,2430,2517,2554,2571,2588,2605,2623,2706,2724,2761,2770,2791,2795,2836,3167,3285,4279,4318,4324,4327,4331,4336,4337] [25,205,214,224,323,326,329,359,361,375,378,381,1631,1644,1647,1650,1657,1672,1721,1724,2240,2249,2259,2269,2285,2296,2306,2322,2333,2376,2443,2452,2459,2462,2469,2472,2480,2484,2488,2530,2536,2558,2646,2665,2699,2702,2712,2736,2739,2774,2778,2782,3052,3065,3068,3071,3078,3093,3105,3115,3142,3145,3180,3197,3306,3459,3481,3489,3525,3529,3769,3786,4070,4084,4105,4128,4138,4155,4175,4362,4584,4606,4611,4631,4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[2,3,2,3],[2,1,3,3],[0,1,2,3]]», by decideFin!⟩
