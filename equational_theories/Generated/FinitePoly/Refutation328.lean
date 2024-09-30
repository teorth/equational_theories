
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(3 * x**2 + 1 * y**2 + 1 * x + 1 * y + 0 * x * y) % 4' (0, 3252, 3260, 3270, 3277, 3305, 3318, 3333, 3345, 3352, 3387, 3413, 4064, 4067, 4070, 4072, 4117, 4119, 4126, 4130, 4134, 4142, 4145, 4274, 4306, 4319, 4361, 4584, 4597, 4655, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 3 * x² + y² + x + y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 3 * x*x + y*y + x + y

/-! The facts -/
theorem «Facts from FinitePoly 3 * x² + y² + x + y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 3334, 3388, 3414, 4135, 4143, 4146, 4307, 4362, 4585, 4673] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3262, 3268, 3269, 3272, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3337, 3342, 3343, 3345, 3352, 3355, 3456, 3543, 3659, 3862, 4055, 4066, 4067, 4070, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4121, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly 3 * x² + y² + x + y % 4», by decideFin!⟩
