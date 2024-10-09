
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 1 * y**2 + 3 * x + 2 * y + 3 * x * y) % 5' (0, 39, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3723, 4269, 4292, 4340, 4589, 4621, 4635)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => x*x + y*y + 3 * x + 2 * y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [40, 4293, 4636] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3664, 3667, 3668, 3674, 3675, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4658] :=
    ⟨Fin 5, «FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5», by decideFin!⟩
