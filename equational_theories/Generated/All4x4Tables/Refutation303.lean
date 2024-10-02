
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 3], [3, 2, 2, 3], [0, 2, 2, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 3], [3, 2, 2, 3], [0, 2, 2, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 3], [3, 2, 2, 3], [0, 2, 2, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 3], [3, 2, 2, 3], [0, 2, 2, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [43, 323, 325, 333, 335, 377, 378, 384, 385, 3308, 3315, 3318, 3345, 3346, 3355, 3509, 3511, 3512, 3519, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3917, 3918, 3924, 3925, 3928, 3951, 3954, 3955, 3961, 4120, 4154, 4155, 4157, 4158, 4165, 4291, 4293, 4321, 4399, 4406, 4436, 4443, 4629, 4636, 4658] [326, 332, 375, 387, 3278, 3309, 3319, 3342, 3352, 3472, 3521, 3522, 3545, 3546, 3715, 3758, 3878, 3915, 3927, 3952, 3964, 4068, 4118, 4121, 4164, 4167, 4284, 4290, 4314, 4320, 4343, 4368, 4396, 4408, 4433, 4445, 4470, 4472, 4473, 4479, 4480, 4598, 4599, 4605, 4606, 4608, 4683] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 3], [3, 2, 2, 3], [0, 2, 2, 3], [3, 3, 3, 3]]», by decideFin!⟩
