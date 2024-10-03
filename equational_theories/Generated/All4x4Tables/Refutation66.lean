import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2259,2296] [211,2266,2269,2277,2281,2285,2303,2306,2314,2318,2322,2330,2333,2368,2372,2376,2449,2452,2459,2462,2469,2472,2480,2484,2488,2662,2665,2699,2702,2736,2739,2774,2778,2782,3052,3068,3071,3078,3093,3255,3264,3265,3306,3458,3464,3467,3525,3529,3664,3684,3712,3769,3786,4128,4138,4269,4316,4318,4584,4631] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,1,2,3],[3,1,2,3],[0,1,2,3]]», by decideFin!⟩
