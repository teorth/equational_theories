
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 2 * x + 2 * y + 1 * x * y) % 3' (0, 358, 3252, 3305, 3861, 3866, 4064, 4069)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + 2 * x + 2 * y + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + 2 * y*y + 2 * x + 2 * y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + 2 * x + 2 * y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [359, 3306, 3867, 4070] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 360, 361, 362, 364, 365, 367, 375, 377, 378, 385, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3337, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3543, 3659, 3864, 3865, 3868, 3870, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4055, 4066, 4067, 4068, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 3, «FinitePoly x² + 2 * y² + 2 * x + 2 * y + x * y % 3», by decideFin!⟩
