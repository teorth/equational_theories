
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 1, 1], [3, 1, 1, 1], [2, 3, 3, 3], [2, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 1, 1], [3, 1, 1, 1], [2, 3, 3, 3], [2, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 1, 1], [3, 1, 1, 1], [2, 3, 3, 3], [2, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 1, 1], [3, 1, 1, 1], [2, 3, 3, 3], [2, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3663, 3947, 4289, 4319, 4342, 4359, 4360] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3863, 3865, 3868, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3917, 3924, 3927, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4055, 4065, 4258, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 1, 1], [3, 1, 1, 1], [2, 3, 3, 3], [2, 3, 3, 3]]», by decideFin!⟩
