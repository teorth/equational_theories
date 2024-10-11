
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 1 * x + 1 * y + 3 * x * y) % 4' (0, 39, 1628, 1636, 1717, 1730, 1745, 3455, 3463, 3471, 3484, 3499, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 4064, 4067, 4089, 4093, 4097, 4130, 4269, 4340, 4589, 4621)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + x + y + 3 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => x*x + 2 * y*y + x + y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + x + y + 3 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [1746, 3485, 4094] [255, 359, 411, 817, 1020, 1635, 1645, 1647, 1658, 1685, 1691, 1729, 1832, 2238, 2441, 2644, 3050, 3253, 3457, 3458, 3459, 3461, 3462, 3465, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3725, 3749, 3759, 3761, 3862, 4066, 4067, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4275, 4290, 4321, 4588, 4598, 4658] :=
    ⟨Fin 4, «FinitePoly x² + 2 * y² + x + y + 3 * x * y % 4», by decideFin!⟩
