
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0,5,0],[2,1,1,1,1,1],[3,4,2,2,2,2],[4,4,5,3,3,3],[4,4,4,4,4,4],[3,3,3,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,3,0,5,0],[2,1,1,1,1,1],[3,4,2,2,2,2],[4,4,5,3,3,3],[4,4,4,4,4,4],[3,3,3,5,5,5]]» : Magma (Fin 6) where
  op := finOpTable "[[0,0,3,0,5,0],[2,1,1,1,1,1],[3,4,2,2,2,2],[4,4,5,3,3,3],[4,4,4,4,4,4],[3,3,3,5,5,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,3,0,5,0],[2,1,1,1,1,1],[3,4,2,2,2,2],[4,4,5,3,3,3],[4,4,4,4,4,4],[3,3,3,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1233] [1026, 1228] :=
    ⟨Fin 6, «All4x4Tables [[0,0,3,0,5,0],[2,1,1,1,1,1],[3,4,2,2,2,2],[4,4,5,3,3,3],[4,4,4,4,4,4],[3,3,3,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
