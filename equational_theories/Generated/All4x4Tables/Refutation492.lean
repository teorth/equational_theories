
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [314, 3886, 4530] [4070, 4071, 4073, 4081, 4083, 4084, 4398, 4406, 4435, 4443, 4472, 4480, 4598, 4606, 4631, 4636, 4647] :=
    ⟨Fin 4, «All4x4Tables [[3,2,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
