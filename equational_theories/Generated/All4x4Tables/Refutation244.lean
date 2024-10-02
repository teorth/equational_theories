
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [323, 2533, 2709, 4362] [23, 47, 308, 309, 310, 312, 313, 315, 325, 326, 333, 335, 1629, 1832, 2444, 2456, 2457, 2459, 2470, 2494, 2496, 2497, 2504, 2530, 2534, 2540, 2645, 2646, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2663, 2669, 2670, 2672, 2673, 2696, 2697, 2699, 2700, 2706, 2707, 2710, 2733, 2734, 2736, 2737, 2743, 2744, 2746, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 4065, 4276, 4293, 4321, 4343, 4585, 4598] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]», by decideFin!⟩
