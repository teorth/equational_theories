
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [363, 4404] [3259, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3342, 3343, 3345, 3346, 3352, 3353, 3462, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3714, 3748, 3749, 3751, 3752, 3759, 3761, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3924, 3938, 3940, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4120, 4155, 4157, 4158, 4164, 4165, 4167, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4320, 4321, 4343, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4587, 4588, 4590, 4591, 4605, 4606, 4608, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]]», by decideFin!⟩
