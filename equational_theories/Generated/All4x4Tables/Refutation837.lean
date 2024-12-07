
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,2,3,3,3],[4,3,3,3,3],[4,3,3,3,3],[3,3,3,3,3],[3,2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,2,3,3,3],[4,3,3,3,3],[4,3,3,3,3],[3,3,3,3,3],[3,2,3,3,3]]» : Magma (Fin 5) where
  op := finOpTable "[[4,2,3,3,3],[4,3,3,3,3],[4,3,3,3,3],[3,3,3,3,3],[3,2,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,2,3,3,3],[4,3,3,3,3],[4,3,3,3,3],[3,3,3,3,3],[3,2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4545] [4396, 4398, 4406, 4408, 4433, 4435, 4443, 4445, 4470, 4472, 4480, 4482, 4583, 4598, 4599, 4605, 4606, 4608, 4622, 4629, 4631, 4635, 4636, 4647] :=
    ⟨Fin 5, «All4x4Tables [[4,2,3,3,3],[4,3,3,3,3],[4,3,3,3,3],[3,3,3,3,3],[3,2,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
