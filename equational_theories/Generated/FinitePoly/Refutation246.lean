
import equational_theories.AllEquations
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
theorem «Facts from FinitePoly y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [2443, 2543, 2646, 2746, 3306] [3, 8, 23, 40, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2446, 2456, 2459, 2466, 2496, 2530, 2649, 2652, 2659, 2662, 2696, 2699, 2706, 2733, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4065, 4270, 4380, 4590] :=
    ⟨Fin 3, «FinitePoly y + x * y % 3», by decideFin!⟩
