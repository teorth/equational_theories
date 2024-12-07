
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,2,4,3,3],[5,3,5,3,0,2],[2,4,2,4,3,3],[4,3,4,3,2,0],[3,0,3,2,4,4],[1,2,1,0,5,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,4,2,4,3,3],[5,3,5,3,0,2],[2,4,2,4,3,3],[4,3,4,3,2,0],[3,0,3,2,4,4],[1,2,1,0,5,4]]» : Magma (Fin 6) where
  op := finOpTable "[[2,4,2,4,3,3],[5,3,5,3,0,2],[2,4,2,4,3,3],[4,3,4,3,2,0],[3,0,3,2,4,4],[1,2,1,0,5,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,4,2,4,3,3],[5,3,5,3,0,2],[2,4,2,4,3,3],[4,3,4,3,2,0],[3,0,3,2,4,4],[1,2,1,0,5,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [365] [4091] :=
    ⟨Fin 6, «All4x4Tables [[2,4,2,4,3,3],[5,3,5,3,0,2],[2,4,2,4,3,3],[4,3,4,3,2,0],[3,0,3,2,4,4],[1,2,1,0,5,4]]», Finite.of_fintype _, by decideFin!⟩
