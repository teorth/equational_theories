
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[1,0,1],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,1],[1,0,1],[1,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[1,0,1],[1,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,1],[1,0,1],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3756, 3823, 4388, 4469] [3253, 3456, 3862, 4065, 4273, 4275, 4290, 4320, 4396, 4598, 4605, 4647, 4656] :=
    ⟨Fin 3, «All4x4Tables [[0,1,1],[1,0,1],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
