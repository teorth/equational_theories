
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 1], [3, 1, 0, 1], [3, 1, 0, 1], [3, 3, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 1], [3, 1, 0, 1], [3, 1, 0, 1], [3, 3, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 1], [3, 1, 0, 1], [3, 1, 0, 1], [3, 3, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 1], [3, 1, 0, 1], [3, 1, 0, 1], [3, 3, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3939, 4360] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 360, 361, 362, 364, 365, 367, 375, 377, 385, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3864, 3865, 3868, 3870, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3925, 3927, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4270, 4272, 4273, 4275, 4276, 4283, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 1], [3, 1, 0, 1], [3, 1, 0, 1], [3, 3, 0, 3]]», by decideFin!⟩
