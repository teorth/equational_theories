import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [669,2863] [1426,1481,2035,2038,2041,2043,2051,2053,2060,2064,2068,2076,2079,2644,2647,2650,2652,2660,2662,2669,2673,2677,2685,2688,2850,2853,2855,2865,2872,2876,2880,2888,2891,3253,3256,3259,3261,3306,3308,3315,3319,3323,3331,3334,3456,3459,3462,3464,3509,3511,3518,3522,3526,3534,3537,3862,3915,3955,4065,4118,4158,4270,4283,4341,4358,4585,4598,4656,4673] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,0,5,4],[2,1,4,5,0,3],[5,4,1,2,3,0],[4,5,0,3,2,1],[3,0,5,4,1,2],[0,3,2,1,4,5]]», by decideFin!⟩
