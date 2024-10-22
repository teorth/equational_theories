
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [314, 3886, 4530] [3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4398, 4399, 4405, 4406, 4435, 4436, 4442, 4443, 4472, 4473, 4479, 4480, 4584, 4585, 4587, 4588, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
