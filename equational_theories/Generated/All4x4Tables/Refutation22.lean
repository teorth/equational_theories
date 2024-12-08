
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,6,7,0],[6,3,4,5,2,7,0,1],[7,0,5,6,3,4,1,2],[4,5,6,3,0,1,2,7],[5,6,7,0,1,2,3,4],[2,7,0,1,6,3,4,5],[3,4,1,2,7,0,5,6],[0,1,2,7,4,5,6,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,4,5,6,7,0],[6,3,4,5,2,7,0,1],[7,0,5,6,3,4,1,2],[4,5,6,3,0,1,2,7],[5,6,7,0,1,2,3,4],[2,7,0,1,6,3,4,5],[3,4,1,2,7,0,5,6],[0,1,2,7,4,5,6,3]]» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,4,5,6,7,0],[6,3,4,5,2,7,0,1],[7,0,5,6,3,4,1,2],[4,5,6,3,0,1,2,7],[5,6,7,0,1,2,3,4],[2,7,0,1,6,3,4,5],[3,4,1,2,7,0,5,6],[0,1,2,7,4,5,6,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,4,5,6,7,0],[6,3,4,5,2,7,0,1],[7,0,5,6,3,4,1,2],[4,5,6,3,0,1,2,7],[5,6,7,0,1,2,3,4],[2,7,0,1,6,3,4,5],[3,4,1,2,7,0,5,6],[0,1,2,7,4,5,6,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1932] [411, 707, 817, 1426, 2035, 3050, 4380] :=
    ⟨Fin 8, «All4x4Tables [[1,2,3,4,5,6,7,0],[6,3,4,5,2,7,0,1],[7,0,5,6,3,4,1,2],[4,5,6,3,0,1,2,7],[5,6,7,0,1,2,3,4],[2,7,0,1,6,3,4,5],[3,4,1,2,7,0,5,6],[0,1,2,7,4,5,6,3]]», Finite.of_fintype _, by decideFin!⟩
