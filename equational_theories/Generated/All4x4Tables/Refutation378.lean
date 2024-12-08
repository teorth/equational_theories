
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1523, 2132, 3497, 3549, 3903, 3917] [1629, 1832, 2238, 2441, 3253, 3459, 3481, 3509, 3518, 3522, 3667, 3675, 3962, 4065, 4273, 4275, 4283, 4290, 4320, 4380, 4598, 4635, 4647] :=
    ⟨Fin 4, «All4x4Tables [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]», Finite.of_fintype _, by decideFin!⟩
