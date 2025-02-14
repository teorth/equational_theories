
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,7,5,0,6,1,3],[0,5,2,1,7,4,3,6],[3,1,4,6,5,0,2,7],[7,2,3,0,4,1,6,5],[1,3,0,7,6,2,5,4],[5,7,6,4,1,3,0,2],[4,6,1,3,2,5,7,0],[6,0,5,2,3,7,4,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,4,7,5,0,6,1,3],[0,5,2,1,7,4,3,6],[3,1,4,6,5,0,2,7],[7,2,3,0,4,1,6,5],[1,3,0,7,6,2,5,4],[5,7,6,4,1,3,0,2],[4,6,1,3,2,5,7,0],[6,0,5,2,3,7,4,1]]» : Magma (Fin 8) where
  op := finOpTable "[[2,4,7,5,0,6,1,3],[0,5,2,1,7,4,3,6],[3,1,4,6,5,0,2,7],[7,2,3,0,4,1,6,5],[1,3,0,7,6,2,5,4],[5,7,6,4,1,3,0,2],[4,6,1,3,2,5,7,0],[6,0,5,2,3,7,4,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,4,7,5,0,6,1,3],[0,5,2,1,7,4,3,6],[3,1,4,6,5,0,2,7],[7,2,3,0,4,1,6,5],[1,3,0,7,6,2,5,4],[5,7,6,4,1,3,0,2],[4,6,1,3,2,5,7,0],[6,0,5,2,3,7,4,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [873] [203, 1223, 4647] :=
    ⟨Fin 8, «All4x4Tables [[2,4,7,5,0,6,1,3],[0,5,2,1,7,4,3,6],[3,1,4,6,5,0,2,7],[7,2,3,0,4,1,6,5],[1,3,0,7,6,2,5,4],[5,7,6,4,1,3,0,2],[4,6,1,3,2,5,7,0],[6,0,5,2,3,7,4,1]]», Finite.of_fintype _, by decideFin!⟩
