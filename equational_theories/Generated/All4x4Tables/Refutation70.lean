
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,1,1],[1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,1,1],[1,0,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,1,1],[1,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,1,1],[1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [379] [307, 3255, 3256, 3258, 3259, 3261, 3262, 3308, 3309, 3456, 3664, 3665, 3667, 3668, 3712, 3714, 3862, 4070, 4071, 4073, 4074, 4118, 4120, 4121, 4268, 4269, 4270, 4283, 4284, 4380, 4584, 4585, 4598, 4599] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,1,1],[1,0,0]]», Finite.of_fintype _, by decideFin!⟩
