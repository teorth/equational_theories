
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,0],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[0,0,0],[0,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,0],[0,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[0,0,0],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [366, 3480, 4444, 4481] [3254, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4275, 4283, 4284, 4290, 4291, 4293, 4396, 4398, 4399, 4405, 4406, 4408] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[0,0,0],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
