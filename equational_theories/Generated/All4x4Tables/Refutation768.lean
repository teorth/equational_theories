
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,0,4,5],[3,1,3,3,1,3],[2,4,2,2,4,2],[3,1,3,3,1,3],[0,4,2,0,4,5],[0,4,5,0,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,5,0,4,5],[3,1,3,3,1,3],[2,4,2,2,4,2],[3,1,3,3,1,3],[0,4,2,0,4,5],[0,4,5,0,4,5]]» : Magma (Fin 6) where
  op := finOpTable "[[0,2,5,0,4,5],[3,1,3,3,1,3],[2,4,2,2,4,2],[3,1,3,3,1,3],[0,4,2,0,4,5],[0,4,5,0,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,5,0,4,5],[3,1,3,3,1,3],[2,4,2,2,4,2],[3,1,3,3,1,3],[0,4,2,0,4,5],[0,4,5,0,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2890] [257, 260, 309, 323] :=
    ⟨Fin 6, «All4x4Tables [[0,2,5,0,4,5],[3,1,3,3,1,3],[2,4,2,2,4,2],[3,1,3,3,1,3],[0,4,2,0,4,5],[0,4,5,0,4,5]]», Finite.of_fintype _, by decideFin!⟩
