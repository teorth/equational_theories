
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 0 * x + 1 * y + 1 * x * y) % 3' (0, 2440, 2442, 2542, 2643, 2645, 2745, 3252, 3305, 4319, 4361)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly y + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2443, 2543, 2646, 2746, 3306] [47, 99, 151, 203, 255, 307, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2442, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2459, 2460, 2466, 2467, 2469, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2645, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2662, 2663, 2669, 2670, 2672, 2673, 2696, 2697, 2699, 2700, 2706, 2707, 2709, 2710, 2733, 2734, 2736, 2737, 2743, 2744, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly y + x * y % 3», Finite.of_fintype _, by decideFin!⟩
