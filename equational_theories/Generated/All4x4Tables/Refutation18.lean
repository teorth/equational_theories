
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[3,1,6,5,2,4,0],[2,5,1,0,4,6,3],[0,6,4,1,3,2,5],[6,3,0,2,1,5,4],[4,0,5,3,6,1,2],[5,4,2,6,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,4,5,0,6],[3,1,6,5,2,4,0],[2,5,1,0,4,6,3],[0,6,4,1,3,2,5],[6,3,0,2,1,5,4],[4,0,5,3,6,1,2],[5,4,2,6,0,3,1]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,3,4,5,0,6],[3,1,6,5,2,4,0],[2,5,1,0,4,6,3],[0,6,4,1,3,2,5],[6,3,0,2,1,5,4],[4,0,5,3,6,1,2],[5,4,2,6,0,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,4,5,0,6],[3,1,6,5,2,4,0],[2,5,1,0,4,6,3],[0,6,4,1,3,2,5],[6,3,0,2,1,5,4],[4,0,5,3,6,1,2],[5,4,2,6,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2244] [1426, 1629, 1832, 2256, 2441, 3050, 3253, 3456, 4065, 4283, 4656] :=
    ⟨Fin 7, «All4x4Tables [[1,2,3,4,5,0,6],[3,1,6,5,2,4,0],[2,5,1,0,4,6,3],[0,6,4,1,3,2,5],[6,3,0,2,1,5,4],[4,0,5,3,6,1,2],[5,4,2,6,0,3,1]]», Finite.of_fintype _, by decideFin!⟩
