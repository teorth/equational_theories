
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]» : Magma (Fin 5) where
  op := finOpTable "[[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [947] [632, 642, 669, 679, 825, 845, 879, 1444, 1451, 1518, 1525, 3915, 3925, 3952, 3962, 4118, 4128, 4155, 4165] :=
    ⟨Fin 5, «All4x4Tables [[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]», Finite.of_fintype _, by decideFin!⟩
