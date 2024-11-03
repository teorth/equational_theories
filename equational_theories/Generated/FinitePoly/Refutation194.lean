
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 0 * y**2 + 2 * x + 0 * y + 1 * x * y) % 4' (0, 39, 358, 359, 366, 367, 368, 377, 3658, 3659, 3660, 3661, 3662, 3664, 3676, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3699, 4064, 4065, 4066, 4067, 4068, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4130, 4269, 4340, 4582, 4589, 4590, 4591, 4596, 4607, 4608, 4621, 4622)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * x + x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => x*x + 2 * x + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * x + x * y % 4» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [368, 378] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4584, 4585, 4587, 4588, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly x² + 2 * x + x * y % 4», Finite.of_fintype _, by decideFin!⟩
