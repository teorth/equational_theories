
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,1],[1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,2],[2,2,1],[1,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[2,2,1],[1,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,2],[2,2,1],[1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1655, 3261] [1832, 2238, 2441, 3050, 3254, 3255, 3256, 3259, 3308, 3315, 3316, 3318, 3319, 3456, 4065, 4268, 4283, 4314, 4585] :=
    ⟨Fin 3, «All4x4Tables [[0,0,2],[2,2,1],[1,0,1]]», Finite.of_fintype _, by decideFin!⟩
