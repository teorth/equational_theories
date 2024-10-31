
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 3 * y**2 + 2 * x + 1 * y + 2 * x * y) % 4' (0, 358, 360, 363, 366, 369, 3252, 3277, 3305, 3352, 3413, 3658, 3663, 3673, 3683, 3693, 3711, 3721, 3731, 3748, 3758, 3768, 3785, 3802, 3819, 3836, 3861, 3863, 3866, 3869, 3872, 3876, 3879, 3882, 3886, 3889, 3892, 3896, 3900, 3904, 3908, 4064, 4066, 4069, 4072, 4075, 4079, 4082, 4085, 4089, 4092, 4095, 4099, 4103, 4107, 4111, 4583, 4586, 4589, 4592, 4598, 4601, 4605, 4610, 4614, 4618, 4621, 4624, 4630, 4634, 4637, 4641, 4644, 4648, 4654, 4662, 4665, 4668, 4674, 4676, 4681, 4688, 4692)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 3 * y² + 2 * x + y + 2 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 3 * y*y + 2 * x + y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 3 * y² + 2 * x + y + 2 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [370, 3414, 3837] [307, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3269, 3271, 3308, 3319, 3346, 3456, 3660, 3661, 3662, 3665, 3667, 3668, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3724, 3725, 3748, 3751, 3752, 3761, 3865, 3868, 3871, 3878, 3881, 3888, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4068, 4071, 4074, 4081, 4084, 4091, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4270, 4275, 4283, 4284, 4314, 4320, 4380] :=
    ⟨Fin 4, «FinitePoly 3 * y² + 2 * x + y + 2 * x * y % 4», Finite.of_fintype _, by decideFin!⟩
