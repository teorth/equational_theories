
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,6,3,7,2,4,0],[2,4,3,6,0,1,5,7],[3,7,2,1,5,6,0,4],[5,1,0,7,3,4,2,6],[4,2,7,0,6,5,1,3],[7,3,4,5,1,0,6,2],[0,6,5,4,2,7,3,1],[6,0,1,2,4,3,7,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,5,6,3,7,2,4,0],[2,4,3,6,0,1,5,7],[3,7,2,1,5,6,0,4],[5,1,0,7,3,4,2,6],[4,2,7,0,6,5,1,3],[7,3,4,5,1,0,6,2],[0,6,5,4,2,7,3,1],[6,0,1,2,4,3,7,5]]» : Magma (Fin 8) where
  op := finOpTable "[[1,5,6,3,7,2,4,0],[2,4,3,6,0,1,5,7],[3,7,2,1,5,6,0,4],[5,1,0,7,3,4,2,6],[4,2,7,0,6,5,1,3],[7,3,4,5,1,0,6,2],[0,6,5,4,2,7,3,1],[6,0,1,2,4,3,7,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,5,6,3,7,2,4,0],[2,4,3,6,0,1,5,7],[3,7,2,1,5,6,0,4],[5,1,0,7,3,4,2,6],[4,2,7,0,6,5,1,3],[7,3,4,5,1,0,6,2],[0,6,5,4,2,7,3,1],[6,0,1,2,4,3,7,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2504] [40, 47, 1629, 1832, 2449, 2457, 3050, 3456, 4065, 4293, 4656] :=
    ⟨Fin 8, «All4x4Tables [[1,5,6,3,7,2,4,0],[2,4,3,6,0,1,5,7],[3,7,2,1,5,6,0,4],[5,1,0,7,3,4,2,6],[4,2,7,0,6,5,1,3],[7,3,4,5,1,0,6,2],[0,6,5,4,2,7,3,1],[6,0,1,2,4,3,7,5]]», Finite.of_fintype _, by decideFin!⟩
