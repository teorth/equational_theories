
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,3,2,0,4],[2,1,0,3,4,5],[3,2,4,0,5,1],[2,1,0,5,4,3],[2,4,0,3,1,5],[4,0,1,3,2,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,5,3,2,0,4],[2,1,0,3,4,5],[3,2,4,0,5,1],[2,1,0,5,4,3],[2,4,0,3,1,5],[4,0,1,3,2,5]]» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,2,0,4],[2,1,0,3,4,5],[3,2,4,0,5,1],[2,1,0,5,4,3],[2,4,0,3,1,5],[4,0,1,3,2,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,5,3,2,0,4],[2,1,0,3,4,5],[3,2,4,0,5,1],[2,1,0,5,4,3],[2,4,0,3,1,5],[4,0,1,3,2,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1082] [4065] :=
    ⟨Fin 6, «All4x4Tables [[1,5,3,2,0,4],[2,1,0,3,4,5],[3,2,4,0,5,1],[2,1,0,5,4,3],[2,4,0,3,1,5],[4,0,1,3,2,5]]», Finite.of_fintype _, by decideFin!⟩
