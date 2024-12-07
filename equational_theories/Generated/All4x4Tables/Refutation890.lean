
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,1,5,3,6,2],[2,0,5,6,0,3,4],[6,0,2,4,5,1,3],[4,5,6,3,2,0,1],[1,6,3,0,2,2,5],[3,2,4,1,6,0,0],[5,3,0,2,1,4,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,4,1,5,3,6,2],[2,0,5,6,0,3,4],[6,0,2,4,5,1,3],[4,5,6,3,2,0,1],[1,6,3,0,2,2,5],[3,2,4,1,6,0,0],[5,3,0,2,1,4,0]]» : Magma (Fin 7) where
  op := finOpTable "[[1,4,1,5,3,6,2],[2,0,5,6,0,3,4],[6,0,2,4,5,1,3],[4,5,6,3,2,0,1],[1,6,3,0,2,2,5],[3,2,4,1,6,0,0],[5,3,0,2,1,4,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,4,1,5,3,6,2],[2,0,5,6,0,3,4],[6,0,2,4,5,1,3],[4,5,6,3,2,0,1],[1,6,3,0,2,2,5],[3,2,4,1,6,0,0],[5,3,0,2,1,4,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3555] [3659] :=
    ⟨Fin 7, «All4x4Tables [[1,4,1,5,3,6,2],[2,0,5,6,0,3,4],[6,0,2,4,5,1,3],[4,5,6,3,2,0,1],[1,6,3,0,2,2,5],[3,2,4,1,6,0,0],[5,3,0,2,1,4,0]]», Finite.of_fintype _, by decideFin!⟩
