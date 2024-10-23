
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 1 * y**2 + 2 * x + 1 * y + 0 * x * y) % 3' (0, 39, 3252, 3254, 3255, 3277, 3278, 3281, 3284, 3285, 3314, 3315, 3318, 3321, 3322, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3723, 3861, 3866, 3869, 3877, 3880, 3890, 3901, 3905, 3914, 3924, 3927, 3934, 3942, 4269, 4292, 4340, 4589, 4621, 4635)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + y² + 2 * x + y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + y*y + 2 * x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + y² + 2 * x + y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3285, 3322, 3323, 3902, 3935, 3943] [47, 99, 151, 203, 255, 307, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3281, 3306, 3308, 3309, 3318, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3660, 3661, 3664, 3667, 3668, 3674, 3675, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3864, 3865, 3868, 3871, 3877, 3880, 3887, 3888, 3890, 3917, 3918, 3924, 3927, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4658] :=
    ⟨Fin 3, «FinitePoly 2 * x² + y² + 2 * x + y % 3», Finite.of_fintype _, by decideFin!⟩
