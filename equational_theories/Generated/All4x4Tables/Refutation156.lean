
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,0,2],[2,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,0,2],[2,0,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,0,2],[2,0,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,0,2],[2,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [841] [108, 414, 427, 430, 436, 437, 439, 440, 823, 842, 843, 845, 846, 1023, 1036, 1039, 1046, 1049, 1252, 1851, 1857, 1860, 1861, 3256, 3278, 3279, 3306, 3315, 3318, 3663, 3665, 3677, 3684, 3685, 3687, 3729, 3865, 3873, 3878, 3881, 3887, 3888, 3943, 4066, 4067, 4068, 4070, 4071, 4073, 4081, 4083, 4084, 4090, 4091, 4093, 4270, 4293, 4314, 4583, 4591, 4606, 4608, 4622, 4631, 4636, 4647] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,0,2],[2,0,2]]», Finite.of_fintype _, by decideFin!⟩
