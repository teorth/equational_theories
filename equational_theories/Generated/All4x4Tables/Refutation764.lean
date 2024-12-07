
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,1,4,4,4],[1,4,2,2,2],[0,0,3,3,3],[1,1,4,4,4],[2,2,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,1,4,4,4],[1,4,2,2,2],[0,0,3,3,3],[1,1,4,4,4],[2,2,2,2,2]]» : Magma (Fin 5) where
  op := finOpTable "[[4,1,4,4,4],[1,4,2,2,2],[0,0,3,3,3],[1,1,4,4,4],[2,2,2,2,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,1,4,4,4],[1,4,2,2,2],[0,0,3,3,3],[1,1,4,4,4],[2,2,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2878] [2852] :=
    ⟨Fin 5, «All4x4Tables [[4,1,4,4,4],[1,4,2,2,2],[0,0,3,3,3],[1,1,4,4,4],[2,2,2,2,2]]», Finite.of_fintype _, by decideFin!⟩
