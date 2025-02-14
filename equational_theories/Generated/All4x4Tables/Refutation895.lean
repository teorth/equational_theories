
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,6,0,4,5,7],[7,0,6,2,4,3,1,5],[3,1,5,7,2,0,4,6],[1,7,3,4,6,5,0,2],[5,2,4,0,7,1,6,3],[0,5,7,1,3,6,2,4],[4,6,2,5,1,7,3,0],[6,4,0,3,5,2,7,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,3,1,6,0,4,5,7],[7,0,6,2,4,3,1,5],[3,1,5,7,2,0,4,6],[1,7,3,4,6,5,0,2],[5,2,4,0,7,1,6,3],[0,5,7,1,3,6,2,4],[4,6,2,5,1,7,3,0],[6,4,0,3,5,2,7,1]]» : Magma (Fin 8) where
  op := finOpTable "[[2,3,1,6,0,4,5,7],[7,0,6,2,4,3,1,5],[3,1,5,7,2,0,4,6],[1,7,3,4,6,5,0,2],[5,2,4,0,7,1,6,3],[0,5,7,1,3,6,2,4],[4,6,2,5,1,7,3,0],[6,4,0,3,5,2,7,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,3,1,6,0,4,5,7],[7,0,6,2,4,3,1,5],[3,1,5,7,2,0,4,6],[1,7,3,4,6,5,0,2],[5,2,4,0,7,1,6,3],[0,5,7,1,3,6,2,4],[4,6,2,5,1,7,3,0],[6,4,0,3,5,2,7,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2734] [99, 411, 2035, 2743, 2847, 4332, 4343] :=
    ⟨Fin 8, «All4x4Tables [[2,3,1,6,0,4,5,7],[7,0,6,2,4,3,1,5],[3,1,5,7,2,0,4,6],[1,7,3,4,6,5,0,2],[5,2,4,0,7,1,6,3],[0,5,7,1,3,6,2,4],[4,6,2,5,1,7,3,0],[6,4,0,3,5,2,7,1]]», Finite.of_fintype _, by decideFin!⟩
