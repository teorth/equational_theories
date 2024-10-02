
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 3], [3, 2, 1, 2], [2, 2, 2, 2], [3, 3, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 3], [3, 2, 1, 2], [2, 2, 2, 2], [3, 3, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 3], [3, 2, 1, 2], [2, 2, 2, 2], [3, 3, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 3], [3, 2, 1, 2], [2, 2, 2, 2], [3, 3, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [359, 835, 843, 846, 3253, 3867, 3870] [99, 360, 361, 362, 364, 365, 367, 375, 377, 378, 385, 818, 833, 1020, 1223, 3259, 3272, 3281, 3308, 3319, 3343, 3352, 3865, 3868, 3871, 3873, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 3], [3, 2, 1, 2], [2, 2, 2, 2], [3, 3, 3, 2]]», by decideFin!⟩
