
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]» : Magma (Fin 8) where
  op := finOpTable "[[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4364] [4358, 4362, 4369, 4380, 4598] :=
    ⟨Fin 8, «All4x4Tables [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
