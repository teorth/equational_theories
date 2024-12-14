
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,2,3,3,5,3],[3,3,3,3,5,3],[5,3,3,3,3,3],[3,3,3,3,3,3],[5,3,3,3,3,3],[3,3,3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,2,3,3,5,3],[3,3,3,3,5,3],[5,3,3,3,3,3],[3,3,3,3,3,3],[5,3,3,3,3,3],[3,3,3,3,3,3]]» : Magma (Fin 6) where
  op := finOpTable "[[4,2,3,3,5,3],[3,3,3,3,5,3],[5,3,3,3,3,3],[3,3,3,3,3,3],[5,3,3,3,3,3],[3,3,3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,2,3,3,5,3],[3,3,3,3,5,3],[5,3,3,3,3,3],[3,3,3,3,3,3],[5,3,3,3,3,3],[3,3,3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4541] [4320, 4435, 4482, 4598] :=
    ⟨Fin 6, «All4x4Tables [[4,2,3,3,5,3],[3,3,3,3,5,3],[5,3,3,3,3,3],[3,3,3,3,3,3],[5,3,3,3,3,3],[3,3,3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
