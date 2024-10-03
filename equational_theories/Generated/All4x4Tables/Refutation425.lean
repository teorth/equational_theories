import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2849,2852,2875,2878] [255,257,260,263,266,307,309,323,326,329,2035,2037,2040,2043,2046,2050,2053,2056,2060,2063,2066,2070,2074,2078,2082,2644,2646,2649,2652,2655,2659,2662,2665,2669,2672,2675,2679,2683,2687,2691,2855,2858,2862,2865,2868,2882,2886,2890,2894,3253,3255,3258,3261,3264,3306,3309,3312,3316,3319,3322,3326,3330,3334,3338,3456,3458,3461,3464,3467,3509,3512,3515,3519,3522,3525,3529,3533,3537,3541,4269,4284,4287,4316,4340,4360,4584,4599,4602,4631,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[1,1,2,1],[3,3,3,3],[3,3,1,3],[0,0,0,0]]», by decideFin!⟩
