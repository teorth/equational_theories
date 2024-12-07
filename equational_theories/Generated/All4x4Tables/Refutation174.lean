
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2],[2,0,0],[0,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,2],[2,0,0],[0,2,1]]» : Magma (Fin 3) where
  op := finOpTable "[[1,0,2],[2,0,0],[0,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,2],[2,0,0],[0,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1685, 1691, 3345, 3353] [255, 411, 817, 1020, 1635, 1637, 1731, 1832, 2035, 2441, 3256, 3278, 3315, 3319, 3659, 3862, 4065, 4270, 4275, 4290, 4598, 4622, 4647] :=
    ⟨Fin 3, «All4x4Tables [[1,0,2],[2,0,0],[0,2,1]]», Finite.of_fintype _, by decideFin!⟩
