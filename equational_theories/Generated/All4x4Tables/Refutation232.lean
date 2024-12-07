
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,2],[1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[0,0,2],[1,2,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[0,0,2],[1,2,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[0,0,2],[1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3343, 3345, 3548, 3555, 4130, 4155, 4157] [3306, 3315, 3319, 3353, 3509, 3518, 3522, 3549, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 4118, 4127, 4131, 4293, 4321, 4606, 4636, 4658] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[0,0,2],[1,2,2]]», Finite.of_fintype _, by decideFin!⟩
