
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,0,6,2,4],[3,3,3,3,3,3,3],[4,6,2,2,0,6,5],[1,1,1,1,1,1,1],[5,0,6,4,4,0,2],[6,5,4,5,2,5,0],[2,4,0,6,5,4,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,5,0,6,2,4],[3,3,3,3,3,3,3],[4,6,2,2,0,6,5],[1,1,1,1,1,1,1],[5,0,6,4,4,0,2],[6,5,4,5,2,5,0],[2,4,0,6,5,4,6]]» : Magma (Fin 7) where
  op := finOpTable "[[0,2,5,0,6,2,4],[3,3,3,3,3,3,3],[4,6,2,2,0,6,5],[1,1,1,1,1,1,1],[5,0,6,4,4,0,2],[6,5,4,5,2,5,0],[2,4,0,6,5,4,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,5,0,6,2,4],[3,3,3,3,3,3,3],[4,6,2,2,0,6,5],[1,1,1,1,1,1,1],[5,0,6,4,4,0,2],[6,5,4,5,2,5,0],[2,4,0,6,5,4,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2450] [3319] :=
    ⟨Fin 7, «All4x4Tables [[0,2,5,0,6,2,4],[3,3,3,3,3,3,3],[4,6,2,2,0,6,5],[1,1,1,1,1,1,1],[5,0,6,4,4,0,2],[6,5,4,5,2,5,0],[2,4,0,6,5,4,6]]», Finite.of_fintype _, by decideFin!⟩
