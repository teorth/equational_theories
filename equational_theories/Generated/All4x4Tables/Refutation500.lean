
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [391, 608, 3993, 3997, 4014, 4027, 4590] [2, 3, 8, 23, 38, 40, 43, 47, 99, 151, 203, 255, 307, 331, 360, 362, 365, 368, 374, 377, 384, 412, 414, 417, 420, 427, 430, 437, 440, 464, 467, 474, 477, 501, 504, 511, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3863, 3865, 3868, 3871, 3878, 3881, 3888, 3917, 3924, 3927, 3951, 3954, 3961, 3964, 4066, 4068, 4071, 4074, 4081, 4084, 4091, 4120, 4127, 4130, 4154, 4157, 4164, 4167, 4268, 4270, 4273, 4276, 4283, 4290, 4293, 4314, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1], [3, 2, 0, 1]]», by decideFin!⟩
