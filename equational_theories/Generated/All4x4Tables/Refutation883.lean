
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]» : Magma (Fin 8) where
  op := finOpTable "[[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [978] [466, 1848] :=
    ⟨Fin 8, «All4x4Tables [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]», Finite.of_fintype _, by decideFin!⟩
