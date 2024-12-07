
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,6,3,6,1,2],[2,5,6,5,6,3,2,3],[7,4,5,0,5,0,7,4],[6,7,2,7,2,1,6,1],[3,6,1,2,1,2,3,6],[4,3,0,3,0,5,4,7],[5,0,7,4,7,4,5,0],[0,1,4,1,4,7,0,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,6,3,6,1,2],[2,5,6,5,6,3,2,3],[7,4,5,0,5,0,7,4],[6,7,2,7,2,1,6,1],[3,6,1,2,1,2,3,6],[4,3,0,3,0,5,4,7],[5,0,7,4,7,4,5,0],[0,1,4,1,4,7,0,5]]» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,6,3,6,1,2],[2,5,6,5,6,3,2,3],[7,4,5,0,5,0,7,4],[6,7,2,7,2,1,6,1],[3,6,1,2,1,2,3,6],[4,3,0,3,0,5,4,7],[5,0,7,4,7,4,5,0],[0,1,4,1,4,7,0,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,6,3,6,1,2],[2,5,6,5,6,3,2,3],[7,4,5,0,5,0,7,4],[6,7,2,7,2,1,6,1],[3,6,1,2,1,2,3,6],[4,3,0,3,0,5,4,7],[5,0,7,4,7,4,5,0],[0,1,4,1,4,7,0,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2853] [2035, 2644, 2855, 2863, 2865, 2872, 3253, 3456, 4270, 4283, 4598, 4656] :=
    ⟨Fin 8, «All4x4Tables [[1,2,3,6,3,6,1,2],[2,5,6,5,6,3,2,3],[7,4,5,0,5,0,7,4],[6,7,2,7,2,1,6,1],[3,6,1,2,1,2,3,6],[4,3,0,3,0,5,4,7],[5,0,7,4,7,4,5,0],[0,1,4,1,4,7,0,5]]», Finite.of_fintype _, by decideFin!⟩
