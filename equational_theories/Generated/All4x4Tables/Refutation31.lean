
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [416, 4090, 4131, 4590] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 412, 413, 414, 417, 419, 420, 426, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]]», by decideFin!⟩
