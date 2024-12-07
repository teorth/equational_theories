
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,2,1],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1],[0,2,1],[2,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,2,1],[2,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1],[0,2,1],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1975, 3901, 3972] [1837, 1857, 2050, 2087, 2124, 3864, 3877, 3887, 3915, 3925, 4067, 4083, 4269, 4284, 4666] :=
    ⟨Fin 3, «All4x4Tables [[0,2,1],[0,2,1],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
