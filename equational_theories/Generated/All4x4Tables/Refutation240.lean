
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[1,2,0],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1],[1,2,0],[2,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[1,2,0],[2,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1],[1,2,0],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [56, 1894, 1931, 2100, 3890] [107, 1020, 1223, 1629, 1837, 1847, 1857, 2050, 2063, 2087, 2124, 3258, 3456, 3877, 3880, 4067, 4083, 4090, 4121, 4320, 4396, 4435, 4445, 4599, 4622] :=
    ⟨Fin 3, «All4x4Tables [[0,2,1],[1,2,0],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
