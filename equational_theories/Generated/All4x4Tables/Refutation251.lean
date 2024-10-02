
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 1, 3], [3, 3, 2, 3], [0, 1, 0, 0], [0, 2, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 1, 3], [3, 3, 2, 3], [0, 1, 0, 0], [0, 2, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 1, 3], [3, 3, 2, 3], [0, 1, 0, 0], [0, 2, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 1, 3], [3, 3, 2, 3], [0, 1, 0, 0], [0, 2, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [257, 263, 2441, 2665, 2672, 2849, 2855, 2865, 2875, 4314] [3, 8, 23, 47, 99, 151, 203, 260, 308, 309, 310, 312, 313, 315, 325, 326, 333, 335, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2443, 2446, 2449, 2456, 2459, 2466, 2469, 2669, 2683, 2687, 2848, 2850, 2852, 2853, 2856, 2862, 2863, 2866, 2872, 2873, 2876, 2899, 2900, 2902, 2903, 2909, 2910, 2912, 2913, 2936, 2937, 2939, 2940, 2946, 2947, 2949, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4055, 4065, 4258, 4284, 4380, 4584, 4599] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 1, 3], [3, 3, 2, 3], [0, 1, 0, 0], [0, 2, 2, 2]]», by decideFin!⟩
