
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 3], [3, 3, 3, 3], [2, 1, 3, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [2, 1, 3, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 3], [3, 3, 3, 3], [2, 1, 3, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [2, 1, 3, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 320, 369, 371, 3297, 3303, 3489, 3502, 3505, 3708, 3913, 4072, 4085, 4099, 4113, 4321, 4346, 4484, 4495, 4497, 4498, 4499, 4609, 4626, 4639] [308, 309, 313, 315, 362, 364, 375, 377, 378, 384, 385, 3255, 3259, 3271, 3279, 3460, 3461, 3475, 3483, 3487, 3666, 3667, 3675, 3679, 3698, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4074, 4080, 4118, 4269, 4273, 4314, 4320, 4383, 4385, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4473, 4479, 4673] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [2, 1, 3, 3], [3, 3, 3, 3]]», by decideFin!⟩
