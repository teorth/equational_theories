
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 0 * x + 0 * y + 0 * x * y) % 3' (0, 42, 306, 325, 331, 358, 374, 386, 3252, 3318, 3341, 3455, 3521, 3544, 3658, 3714, 3757, 3861, 3914, 3963, 4064, 4117, 4166, 4282, 4342, 4357, 4379, 4397, 4404, 4434, 4441, 4469, 4481, 4530, 4543, 4607, 4634, 4676)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y² % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [332] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3306, 3308, 3309, 3315, 3316, 3318, 3343, 3345, 3346, 3352, 3353, 3355, 3509, 3511, 3512, 3518, 3519, 3521, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4396, 4399, 4406, 4408, 4433, 4436, 4443, 4445, 4472, 4473, 4479, 4480, 4598, 4599, 4605, 4606, 4629, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y² % 3», by decideFin!⟩
