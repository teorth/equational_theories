
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [369, 3700, 4099, 4113, 4282, 4288, 4592, 4609] [2, 3, 8, 23, 38, 39, 43, 47, 99, 151, 203, 255, 307, 331, 361, 362, 364, 365, 374, 375, 377, 378, 384, 385, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3862, 4055, 4071, 4074, 4080, 4083, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4269, 4272, 4273, 4275, 4276, 4283, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4584, 4585, 4587, 4588, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]», by decideFin!⟩
