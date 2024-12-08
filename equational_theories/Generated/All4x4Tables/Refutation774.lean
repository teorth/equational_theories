
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,4,5,2],[5,3,2,3,5,3],[5,5,3,0,0,4],[0,5,4,0,0,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,4,4,5,2],[5,3,2,3,5,3],[5,5,3,0,0,4],[0,5,4,0,0,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,4,5,2],[5,3,2,3,5,3],[5,5,3,0,0,4],[0,5,4,0,0,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,4,4,5,2],[5,3,2,3,5,3],[5,5,3,0,0,4],[0,5,4,0,0,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2994] [2644, 3253, 3456] :=
    ⟨Fin 6, «All4x4Tables [[1,2,4,4,5,2],[5,3,2,3,5,3],[5,5,3,0,0,4],[0,5,4,0,0,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]», Finite.of_fintype _, by decideFin!⟩
