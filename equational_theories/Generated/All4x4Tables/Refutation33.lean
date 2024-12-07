
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2900] [411, 614, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 3050, 3659, 4380] :=
    ⟨Fin 7, «All4x4Tables [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]», Finite.of_fintype _, by decideFin!⟩
