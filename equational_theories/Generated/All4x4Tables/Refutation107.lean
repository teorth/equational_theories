import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2290,2372,2406] [211,224,242,309,323,1631,1644,1647,1650,1657,1672,1721,1724,2253,2269,2273,2277,2281,2285,2293,2296,2300,2303,2306,2310,2314,2318,2322,2333,2368,2376,2385,2389,2402,2420,2425,2443,2452,2462,2472,2476,2480,2484,2488,2517,2536,2558,2571,2588,2623,2646,2665,2699,2702,2712,2739,2774,2778,2782,3052,3068,3071,3078,3093,3105,3115,3142,3145,3180,3197,3255,3261,3264,3271,3274,3306,3456,3461,3464,3467,3481,3509,3519,3522,3525,3529,3659,3674,3684,3712,3769,3786,4070,4090,4118,4128,4131,4138,4155,4175,4269,4316,4320,4327,4362,4584,4606,4611,4631] :=
    ⟨Fin 4, «FinitePoly [[1,3,2,3],[3,3,3,3],[1,2,3,3],[0,1,2,3]]», by decideFin!⟩
