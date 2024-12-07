
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,4,2,0],[3,2,1,1,5,2],[3,2,2,1,5,1],[3,3,2,2,5,1],[2,1,4,4,1,0],[3,2,2,1,5,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,0,4,2,0],[3,2,1,1,5,2],[3,2,2,1,5,1],[3,3,2,2,5,1],[2,1,4,4,1,0],[3,2,2,1,5,2]]» : Magma (Fin 6) where
  op := finOpTable "[[1,0,0,4,2,0],[3,2,1,1,5,2],[3,2,2,1,5,1],[3,3,2,2,5,1],[2,1,4,4,1,0],[3,2,2,1,5,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,0,4,2,0],[3,2,1,1,5,2],[3,2,2,1,5,1],[3,3,2,2,5,1],[2,1,4,4,1,0],[3,2,2,1,5,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3279] [3255, 3256, 3278, 3306, 3659, 4065, 4269, 4270, 4314, 4606, 4622, 4631] :=
    ⟨Fin 6, «All4x4Tables [[1,0,0,4,2,0],[3,2,1,1,5,2],[3,2,2,1,5,1],[3,3,2,2,5,1],[2,1,4,4,1,0],[3,2,2,1,5,2]]», Finite.of_fintype _, by decideFin!⟩
