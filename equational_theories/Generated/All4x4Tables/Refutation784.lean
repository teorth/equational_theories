
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,5,3,2,4,2],[5,2,2,4,3,0],[3,1,2,0,3,0],[2,4,0,3,2,5],[0,5,3,2,0,2],[2,4,0,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,5,3,2,4,2],[5,2,2,4,3,0],[3,1,2,0,3,0],[2,4,0,3,2,5],[0,5,3,2,0,2],[2,4,0,3,2,3]]» : Magma (Fin 6) where
  op := finOpTable "[[0,5,3,2,4,2],[5,2,2,4,3,0],[3,1,2,0,3,0],[2,4,0,3,2,5],[0,5,3,2,0,2],[2,4,0,3,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,5,3,2,4,2],[5,2,2,4,3,0],[3,1,2,0,3,0],[2,4,0,3,2,5],[0,5,3,2,0,2],[2,4,0,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [313] [3272] :=
    ⟨Fin 6, «All4x4Tables [[0,5,3,2,4,2],[5,2,2,4,3,0],[3,1,2,0,3,0],[2,4,0,3,2,5],[0,5,3,2,0,2],[2,4,0,3,2,3]]», Finite.of_fintype _, by decideFin!⟩
