
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2910] [56, 2035, 2644] :=
    ⟨Fin 7, «All4x4Tables [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]», Finite.of_fintype _, by decideFin!⟩
