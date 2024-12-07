
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1445, 1489, 1516] [614, 817, 1482, 1832, 3253, 3456, 4065, 4283, 4284, 4293, 4314, 4591, 4599] :=
    ⟨Fin 7, «All4x4Tables [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]», Finite.of_fintype _, by decideFin!⟩
