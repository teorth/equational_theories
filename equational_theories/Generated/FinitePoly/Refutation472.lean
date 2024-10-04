
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(3 * x**2 + 0 * y**2 + 0 * x + 0 * y + 2 * x * y) % 5' (0, 39, 358, 359, 366, 367, 368, 3658, 3659, 3660, 3661, 3662, 3664, 3676, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3699, 4064, 4065, 4066, 4067, 4068, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4269, 4340, 4582, 4589, 4590, 4591, 4596, 4607, 4608, 4621, 4622)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 3 * x² + 2 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 3 * x*x + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 3 * x² + 2 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [368] [4131] :=
    ⟨Fin 5, «FinitePoly 3 * x² + 2 * x * y % 5», by decideFin!⟩
