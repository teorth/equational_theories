
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]» : Magma (Fin 6) where
  op := finOpTable "[[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2381, 2398] [2503, 3306, 3309, 3316, 3343, 3346, 3353, 3509, 3519, 3546, 3556, 3712, 3749, 3752, 3759, 3897, 3925, 3952, 3962, 4128, 4165, 4284, 4320, 4396, 4406, 4435, 4445, 4480, 4606] :=
    ⟨Fin 6, «All4x4Tables [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]», Finite.of_fintype _, by decideFin!⟩
