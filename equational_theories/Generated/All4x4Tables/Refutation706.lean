
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,2,2,2],[3,3,3,4,3,4],[5,0,0,0,5,0],[1,1,1,1,1,1],[5,5,5,1,5,1],[2,4,4,4,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,2,2,2,2,2],[3,3,3,4,3,4],[5,0,0,0,5,0],[1,1,1,1,1,1],[5,5,5,1,5,1],[2,4,4,4,2,4]]» : Magma (Fin 6) where
  op := finOpTable "[[2,2,2,2,2,2],[3,3,3,4,3,4],[5,0,0,0,5,0],[1,1,1,1,1,1],[5,5,5,1,5,1],[2,4,4,4,2,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,2,2,2,2,2],[3,3,3,4,3,4],[5,0,0,0,5,0],[1,1,1,1,1,1],[5,5,5,1,5,1],[2,4,4,4,2,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1448] [1435, 1638, 3261, 3262, 3462, 3465, 3518, 3521, 4314] :=
    ⟨Fin 6, «All4x4Tables [[2,2,2,2,2,2],[3,3,3,4,3,4],[5,0,0,0,5,0],[1,1,1,1,1,1],[5,5,5,1,5,1],[2,4,4,4,2,4]]», Finite.of_fintype _, by decideFin!⟩
