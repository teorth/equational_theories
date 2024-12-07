
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,2,5,2],[4,3,2,3,0,3],[3,4,5,4,1,4],[0,5,4,5,2,5],[5,0,1,0,3,0],[2,1,0,1,4,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,2,5,2],[4,3,2,3,0,3],[3,4,5,4,1,4],[0,5,4,5,2,5],[5,0,1,0,3,0],[2,1,0,1,4,1]]» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,2,5,2],[4,3,2,3,0,3],[3,4,5,4,1,4],[0,5,4,5,2,5],[5,0,1,0,3,0],[2,1,0,1,4,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,2,5,2],[4,3,2,3,0,3],[3,4,5,4,1,4],[0,5,4,5,2,5],[5,0,1,0,3,0],[2,1,0,1,4,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2880] [3253, 3456] :=
    ⟨Fin 6, «All4x4Tables [[1,2,3,2,5,2],[4,3,2,3,0,3],[3,4,5,4,1,4],[0,5,4,5,2,5],[5,0,1,0,3,0],[2,1,0,1,4,1]]», Finite.of_fintype _, by decideFin!⟩
