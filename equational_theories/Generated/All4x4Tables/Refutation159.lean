
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,2,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[0,2,0],[0,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[0,2,0],[0,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[0,2,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4301, 4425, 4462] [4270, 4272, 4284, 4290, 4314, 4320, 4343, 4358, 4396, 4398, 4406, 4408, 4433, 4435, 4443, 4445, 4470, 4472, 4473, 4480, 4482, 4583, 4598, 4599, 4606, 4608, 4622, 4631, 4636, 4647] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[0,2,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
