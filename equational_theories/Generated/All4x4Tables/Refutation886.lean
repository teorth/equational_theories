
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,4,4,3,2],[0,2,4,2,4,5],[0,3,2,2,2,5],[5,2,2,2,1,0],[5,1,1,1,2,0],[2,4,4,4,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,4,4,4,3,2],[0,2,4,2,4,5],[0,3,2,2,2,5],[5,2,2,2,1,0],[5,1,1,1,2,0],[2,4,4,4,3,1]]» : Magma (Fin 6) where
  op := finOpTable "[[1,4,4,4,3,2],[0,2,4,2,4,5],[0,3,2,2,2,5],[5,2,2,2,1,0],[5,1,1,1,2,0],[2,4,4,4,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,4,4,4,3,2],[0,2,4,2,4,5],[0,3,2,2,2,5],[5,2,2,2,1,0],[5,1,1,1,2,0],[2,4,4,4,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4084] [3253, 3659, 4068, 4070, 4090, 4131, 4269, 4270, 4314, 4606, 4622, 4631] :=
    ⟨Fin 6, «All4x4Tables [[1,4,4,4,3,2],[0,2,4,2,4,5],[0,3,2,2,2,5],[5,2,2,2,1,0],[5,1,1,1,2,0],[2,4,4,4,3,1]]», Finite.of_fintype _, by decideFin!⟩
