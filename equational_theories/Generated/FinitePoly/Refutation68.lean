
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 1 * x + 1 * y + 2 * x * y) % 3' (0, 306, 2034, 2049, 3252, 3658, 3659)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + x + y + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + 2 * y*y + x + y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + x + y + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [307, 2050, 3660] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2036, 2037, 2038, 2040, 2041, 2043, 2044, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly x² + 2 * y² + x + y + 2 * x * y % 3», Finite.of_fintype _, by decideFin!⟩
