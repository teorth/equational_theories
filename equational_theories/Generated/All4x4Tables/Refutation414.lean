
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [655, 861] [3456, 3665, 3667, 3865, 3868, 4065, 4283, 4673] :=
    ⟨Fin 4, «All4x4Tables [[1,0,0,1],[3,1,1,3],[3,2,2,0],[1,3,3,2]]», Finite.of_fintype _, by decideFin!⟩
