
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,4,4,0,4,0,0],[2,2,3,1,1,3,2],[3,2,3,6,2,3,2],[3,2,3,6,3,3,5],[0,4,4,4,4,4,4],[5,5,3,6,5,3,5],[6,5,3,6,6,3,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,4,4,0,4,0,0],[2,2,3,1,1,3,2],[3,2,3,6,2,3,2],[3,2,3,6,3,3,5],[0,4,4,4,4,4,4],[5,5,3,6,5,3,5],[6,5,3,6,6,3,5]]» : Magma (Fin 7) where
  op := finOpTable "[[0,4,4,0,4,0,0],[2,2,3,1,1,3,2],[3,2,3,6,2,3,2],[3,2,3,6,3,3,5],[0,4,4,4,4,4,4],[5,5,3,6,5,3,5],[6,5,3,6,6,3,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,4,4,0,4,0,0],[2,2,3,1,1,3,2],[3,2,3,6,2,3,2],[3,2,3,6,3,3,5],[0,4,4,4,4,4,4],[5,5,3,6,5,3,5],[6,5,3,6,6,3,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [856] [639, 642, 842, 1426, 4131] :=
    ⟨Fin 7, «All4x4Tables [[0,4,4,0,4,0,0],[2,2,3,1,1,3,2],[3,2,3,6,2,3,2],[3,2,3,6,3,3,5],[0,4,4,4,4,4,4],[5,5,3,6,5,3,5],[6,5,3,6,6,3,5]]», Finite.of_fintype _, by decideFin!⟩
