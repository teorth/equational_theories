
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,1,3],[1,1,0,0],[3,3,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,3,1,3],[3,3,1,3],[1,1,0,0],[3,3,1,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[3,3,1,3],[1,1,0,0],[3,3,1,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,3,1,3],[3,3,1,3],[1,1,0,0],[3,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4419] [4270, 4272, 4275, 4276, 4284, 4290, 4293, 4343, 4396, 4399, 4406, 4470, 4472, 4473, 4479, 4480, 4482, 4583, 4591, 4598, 4605, 4608, 4629, 4636, 4647, 4656, 4658] :=
    ⟨Fin 4, «All4x4Tables [[3,3,1,3],[3,3,1,3],[1,1,0,0],[3,3,1,3]]», Finite.of_fintype _, by decideFin!⟩
