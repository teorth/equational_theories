
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]» : Magma (Fin 7) where
  op := finOpTable "[[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [261, 2061] [2660, 2669, 2852, 2856, 2865, 2873, 3255, 3256, 3315, 3316, 3318, 3457, 3458, 3519, 3521, 4268, 4598, 4656] :=
    ⟨Fin 7, «All4x4Tables [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]», Finite.of_fintype _, by decideFin!⟩
