
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1797] [99, 151, 817, 1223, 1426, 1638, 1838, 1848, 1858, 2035, 3259, 3262, 3308, 3456, 3659, 4065, 4283, 4314] :=
    ⟨Fin 4, «All4x4Tables [[2,3,0,1],[1,0,3,2],[1,0,3,2],[2,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
