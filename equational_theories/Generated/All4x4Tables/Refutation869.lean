
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,0,4,1,0,0],[2,6,1,6,2,1,1],[3,2,5,5,2,5,2],[3,2,5,5,2,5,3],[6,6,4,6,6,4,4],[5,5,6,6,5,6,5],[6,6,6,6,6,6,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,1,0,4,1,0,0],[2,6,1,6,2,1,1],[3,2,5,5,2,5,2],[3,2,5,5,2,5,3],[6,6,4,6,6,4,4],[5,5,6,6,5,6,5],[6,6,6,6,6,6,6]]» : Magma (Fin 7) where
  op := finOpTable "[[1,1,0,4,1,0,0],[2,6,1,6,2,1,1],[3,2,5,5,2,5,2],[3,2,5,5,2,5,3],[6,6,4,6,6,4,4],[5,5,6,6,5,6,5],[6,6,6,6,6,6,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,1,0,4,1,0,0],[2,6,1,6,2,1,1],[3,2,5,5,2,5,2],[3,2,5,5,2,5,3],[6,6,4,6,6,4,4],[5,5,6,6,5,6,5],[6,6,6,6,6,6,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [837] [1223] :=
    ⟨Fin 7, «All4x4Tables [[1,1,0,4,1,0,0],[2,6,1,6,2,1,1],[3,2,5,5,2,5,2],[3,2,5,5,2,5,3],[6,6,4,6,6,4,4],[5,5,6,6,5,6,5],[6,6,6,6,6,6,6]]», Finite.of_fintype _, by decideFin!⟩
