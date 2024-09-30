
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [369, 378, 3684, 3685, 3687, 4099, 4341, 4609] [8, 99, 361, 362, 364, 365, 374, 375, 377, 384, 385, 411, 817, 1020, 1223, 1832, 3253, 3721, 3724, 3725, 3862, 4070, 4071, 4073, 4081, 4083, 4084, 4269, 4293, 4314, 4584, 4588, 4598, 4606, 4636] :=
    ⟨Fin 4, «FinitePoly x² + 2 * x + x * y % 4», by decideFin!⟩
