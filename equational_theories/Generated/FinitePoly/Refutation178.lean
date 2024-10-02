
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 3 * y**2 + 0 * x + 2 * y + 3 * x * y) % 4' (0, 3252, 3257, 3261, 3305, 4275)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 3 * y² + 2 * y + 3 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + 3 * y*y + 2 * y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 3 * y² + 2 * y + 3 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [3258, 3262, 3306, 4276] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3259, 3261, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly 2 * x² + 3 * y² + 2 * y + 3 * x * y % 4», by decideFin!⟩
