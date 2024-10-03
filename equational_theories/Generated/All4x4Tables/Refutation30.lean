import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [266,307,323,2652,2659,2665,2672,2675,2679,2683,2687,2691,2855,2858,2865,2868,2872,2886,2890,2894,4314,4584,4599,4602,4631,4655,4675] [326,2035,2038,2040,2041,2043,2050,2051,2053,2060,2063,2064,2068,2070,2076,2078,2079,2647,2650,2660,2673,2677,2685,2688,2850,2853,2863,2876,2880,2888,2891,3255,3256,3259,3261,3308,3309,3315,3316,3319,3322,3323,3331,3334,3456,3458,3459,3461,3462,3464,3467,3509,3511,3512,3518,3519,3522,3525,3526,3529,3533,3534,3537,3659,3712,4065,4067,4068,4070,4073,4076,4118,4128,4131,4269,4270,4283,4284,4316,4318,4341,4358,4585,4598,4606,4656,4673] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,1],[2,2,2,2],[0,0,3,3],[1,1,1,1]]», by decideFin!⟩
