
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 1 * y**2 + 1 * x + 2 * y + 1 * x * y) % 3' (0, 39, 3252, 3255, 3277, 3281, 3285, 3658, 3661, 3663, 3664, 3667, 3671, 3673, 3676, 3677, 3681, 3683, 3687, 3691, 3693, 3698, 3699, 3703, 3708, 3711, 3748, 3758, 3819, 4064, 4067, 4089, 4093, 4097, 4269, 4320, 4340, 4589, 4621, 4657)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + y² + x + 2 * y + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + y*y + x + 2 * y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + y² + x + 2 * y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3282, 3709, 3749, 3820, 4094, 4321, 4658] [47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3660, 3661, 3667, 3675, 3685, 3687, 3714, 3721, 3722, 3724, 3725, 3748, 3751, 3752, 3761, 3769, 3786, 3862, 4066, 4067, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 3, «FinitePoly x² + y² + x + 2 * y + x * y % 3», Finite.of_fintype _, by decideFin!⟩
