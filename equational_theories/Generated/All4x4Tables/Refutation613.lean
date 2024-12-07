
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1060] [1242] :=
    ⟨Fin 4, «All4x4Tables [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
