
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,6,3,4,5,3,2],[2,1,2,1,1,5,1],[6,2,2,2,5,6,4],[5,1,2,3,3,5,1],[3,1,6,3,4,4,6],[4,5,4,5,4,5,5],[1,1,5,1,6,5,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,6,3,4,5,3,2],[2,1,2,1,1,5,1],[6,2,2,2,5,6,4],[5,1,2,3,3,5,1],[3,1,6,3,4,4,6],[4,5,4,5,4,5,5],[1,1,5,1,6,5,6]]» : Magma (Fin 7) where
  op := finOpTable "[[1,6,3,4,5,3,2],[2,1,2,1,1,5,1],[6,2,2,2,5,6,4],[5,1,2,3,3,5,1],[3,1,6,3,4,4,6],[4,5,4,5,4,5,5],[1,1,5,1,6,5,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,6,3,4,5,3,2],[2,1,2,1,1,5,1],[6,2,2,2,5,6,4],[5,1,2,3,3,5,1],[3,1,6,3,4,4,6],[4,5,4,5,4,5,5],[1,1,5,1,6,5,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3961] [3456, 3917, 4293] :=
    ⟨Fin 7, «All4x4Tables [[1,6,3,4,5,3,2],[2,1,2,1,1,5,1],[6,2,2,2,5,6,4],[5,1,2,3,3,5,1],[3,1,6,3,4,4,6],[4,5,4,5,4,5,5],[1,1,5,1,6,5,6]]», Finite.of_fintype _, by decideFin!⟩
