
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,3,1,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,3,1,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2415] [3306, 3346, 3353, 3546, 3556, 3752, 3759, 3925, 3952, 3962, 4128, 4165, 4320, 4435, 4445, 4480, 4606] :=
    ⟨Fin 4, «All4x4Tables [[0,3,1,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
