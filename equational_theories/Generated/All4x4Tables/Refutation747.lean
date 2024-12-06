
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,2,3,2,2],[2,1,2,1,4,5],[5,1,5,3,5,5],[0,3,2,3,4,5],[2,1,2,3,2,2],[0,1,4,3,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,3,2,3,2,2],[2,1,2,1,4,5],[5,1,5,3,5,5],[0,3,2,3,4,5],[2,1,2,3,2,2],[0,1,4,3,4,4]]» : Magma (Fin 6) where
  op := finOpTable "[[2,3,2,3,2,2],[2,1,2,1,4,5],[5,1,5,3,5,5],[0,3,2,3,4,5],[2,1,2,3,2,2],[0,1,4,3,4,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,3,2,3,2,2],[2,1,2,1,4,5],[5,1,5,3,5,5],[0,3,2,3,4,5],[2,1,2,3,2,2],[0,1,4,3,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2683] [2652] :=
    ⟨Fin 6, «All4x4Tables [[2,3,2,3,2,2],[2,1,2,1,4,5],[5,1,5,3,5,5],[0,3,2,3,4,5],[2,1,2,3,2,2],[0,1,4,3,4,4]]», Finite.of_fintype _, by decideFin!⟩
