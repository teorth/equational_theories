
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [864] [1426, 3862, 4073, 4118, 4121, 4128, 4599] :=
    ⟨Fin 4, «All4x4Tables [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]», Finite.of_fintype _, by decideFin!⟩
