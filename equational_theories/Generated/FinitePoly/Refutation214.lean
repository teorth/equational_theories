
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 2 * x + 2 * y + 2 * x * y) % 3' (0, 306, 3252, 3254, 3455, 3457, 4064, 4130)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + 2 * x + 2 * y + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + 2 * y*y + 2 * x + 2 * y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + 2 * x + 2 * y + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [307, 3255, 3458] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 308, 309, 310, 312, 313, 315, 316, 323, 325, 326, 331, 332, 333, 335, 336, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3337, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3457, 3459, 3461, 3462, 3464, 3465, 3471, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3543, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4055, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 3, «FinitePoly x² + 2 * y² + 2 * x + 2 * y + 2 * x * y % 3», by decideFin!⟩
