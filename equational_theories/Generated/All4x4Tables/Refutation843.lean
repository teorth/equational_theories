
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6]]» : Magma (Fin 7) where
  op := finOpTable "[[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [476, 503, 510] [3915, 3955, 4083, 4118, 4158] :=
    ⟨Fin 7, «All4x4Tables [[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6],[2,4,3,5,6,0,1],[2,1,3,5,4,0,6]]», Finite.of_fintype _, by decideFin!⟩
