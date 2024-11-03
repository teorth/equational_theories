
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,0],[0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,0],[0,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,0],[0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,0],[0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [314, 3886, 4524, 4530] [3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4074, 4080, 4118, 4120, 4121, 4127, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4399, 4405, 4436, 4442, 4473, 4479, 4585, 4587, 4599, 4605, 4629, 4635, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,0],[0,2,0]]», Finite.of_fintype _, by decideFin!⟩
