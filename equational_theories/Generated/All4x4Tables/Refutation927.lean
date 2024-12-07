
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,2,4,5,6,7],[2,5,3,4,0,1,6,7],[4,1,3,2,0,5,6,7],[1,0,3,2,7,5,6,4],[6,1,3,2,4,5,0,7],[4,5,0,2,3,1,6,7],[0,1,3,2,4,5,6,7],[1,0,3,2,4,5,6,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,3,2,4,5,6,7],[2,5,3,4,0,1,6,7],[4,1,3,2,0,5,6,7],[1,0,3,2,7,5,6,4],[6,1,3,2,4,5,0,7],[4,5,0,2,3,1,6,7],[0,1,3,2,4,5,6,7],[1,0,3,2,4,5,6,7]]» : Magma (Fin 8) where
  op := finOpTable "[[1,0,3,2,4,5,6,7],[2,5,3,4,0,1,6,7],[4,1,3,2,0,5,6,7],[1,0,3,2,7,5,6,4],[6,1,3,2,4,5,0,7],[4,5,0,2,3,1,6,7],[0,1,3,2,4,5,6,7],[1,0,3,2,4,5,6,7]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,3,2,4,5,6,7],[2,5,3,4,0,1,6,7],[4,1,3,2,0,5,6,7],[1,0,3,2,7,5,6,4],[6,1,3,2,4,5,0,7],[4,5,0,2,3,1,6,7],[0,1,3,2,4,5,6,7],[1,0,3,2,4,5,6,7]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1112] [1629] :=
    ⟨Fin 8, «All4x4Tables [[1,0,3,2,4,5,6,7],[2,5,3,4,0,1,6,7],[4,1,3,2,0,5,6,7],[1,0,3,2,7,5,6,4],[6,1,3,2,4,5,0,7],[4,5,0,2,3,1,6,7],[0,1,3,2,4,5,6,7],[1,0,3,2,4,5,6,7]]», Finite.of_fintype _, by decideFin!⟩
