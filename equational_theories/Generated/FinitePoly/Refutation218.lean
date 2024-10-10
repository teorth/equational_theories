
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 1 * x + 2 * y + 0 * x * y) % 3' (0, 39, 3455, 3457, 3463, 3471, 3481, 3484, 3487, 3499, 3508, 3518, 3521, 3524, 3536, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3748, 4064, 4067, 4069, 4083, 4089, 4093, 4097, 4104, 4117, 4127, 4137, 4164, 4225, 4269, 4320, 4340, 4589, 4621, 4657)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + x + 2 * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + 2 * y*y + x + 2 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + x + 2 * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [3488, 3525, 3537, 3749, 4105, 4138, 4226, 4321, 4658] [47, 99, 151, 203, 255, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3457, 3459, 3461, 3462, 3465, 3474, 3475, 3481, 3484, 3511, 3512, 3518, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3660, 3661, 3664, 3667, 3668, 3674, 3675, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3751, 3752, 3759, 3761, 3862, 4066, 4067, 4071, 4073, 4074, 4080, 4081, 4083, 4091, 4093, 4120, 4121, 4127, 4130, 4131, 4155, 4157, 4158, 4164, 4167, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 3, «FinitePoly x² + 2 * y² + x + 2 * y % 3», by decideFin!⟩
