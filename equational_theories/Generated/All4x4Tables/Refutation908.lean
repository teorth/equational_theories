
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,0,2,5,0,5,4],[0,3,0,3,0,0,3,3],[0,3,0,3,0,0,3,3],[1,3,6,1,7,6,7,3],[1,3,0,1,7,0,7,3],[4,4,6,4,6,6,6,4],[2,4,6,2,5,6,5,4],[4,4,6,4,6,6,6,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,4,0,2,5,0,5,4],[0,3,0,3,0,0,3,3],[0,3,0,3,0,0,3,3],[1,3,6,1,7,6,7,3],[1,3,0,1,7,0,7,3],[4,4,6,4,6,6,6,4],[2,4,6,2,5,6,5,4],[4,4,6,4,6,6,6,4]]» : Magma (Fin 8) where
  op := finOpTable "[[2,4,0,2,5,0,5,4],[0,3,0,3,0,0,3,3],[0,3,0,3,0,0,3,3],[1,3,6,1,7,6,7,3],[1,3,0,1,7,0,7,3],[4,4,6,4,6,6,6,4],[2,4,6,2,5,6,5,4],[4,4,6,4,6,6,6,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,4,0,2,5,0,5,4],[0,3,0,3,0,0,3,3],[0,3,0,3,0,0,3,3],[1,3,6,1,7,6,7,3],[1,3,0,1,7,0,7,3],[4,4,6,4,6,6,6,4],[2,4,6,2,5,6,5,4],[4,4,6,4,6,6,6,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2162] [3462, 3521, 3880, 3952, 4314, 4606] :=
    ⟨Fin 8, «All4x4Tables [[2,4,0,2,5,0,5,4],[0,3,0,3,0,0,3,3],[0,3,0,3,0,0,3,3],[1,3,6,1,7,6,7,3],[1,3,0,1,7,0,7,3],[4,4,6,4,6,6,6,4],[2,4,6,2,5,6,5,4],[4,4,6,4,6,6,6,4]]», Finite.of_fintype _, by decideFin!⟩
