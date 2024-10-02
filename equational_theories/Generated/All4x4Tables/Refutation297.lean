
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 2, 3], [3, 2, 0, 3], [2, 0, 2, 0], [3, 3, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 2, 3], [3, 2, 0, 3], [2, 0, 2, 0], [3, 3, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 2, 3], [3, 2, 0, 3], [2, 0, 2, 0], [3, 3, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 2, 3], [3, 2, 0, 3], [2, 0, 2, 0], [3, 3, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3659, 3954, 4065, 4482] [43, 307, 359, 1426, 1629, 1832, 2035, 3253, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3955, 3961, 3962, 3964, 4081, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 2, 3], [3, 2, 0, 3], [2, 0, 2, 0], [3, 3, 0, 3]]», by decideFin!⟩
