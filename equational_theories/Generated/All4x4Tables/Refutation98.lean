
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,2,1],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1],[0,2,1],[2,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,2,1],[2,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1],[0,2,1],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1847, 1887, 1921, 3935, 4023] [1109, 1122, 1629, 1857, 3659, 4065, 4269, 4270, 4273, 4275, 4283, 4290, 4314, 4320, 4380, 4583, 4598, 4605, 4622, 4635, 4647, 4656] :=
    ⟨Fin 3, «All4x4Tables [[0,2,1],[0,2,1],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
