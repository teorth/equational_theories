
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1285, 1313] [56, 411, 614, 817, 1020, 1241, 1426, 1629, 1832, 2035, 2238, 2441, 2847, 3050, 3253, 3456, 3862, 4065, 4275, 4380, 4635] :=
    ⟨Fin 7, «All4x4Tables [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]», Finite.of_fintype _, by decideFin!⟩
