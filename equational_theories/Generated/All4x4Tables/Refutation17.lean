
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,6,0],[3,4,5,6,0,1,2],[5,6,0,1,2,3,4],[0,1,2,3,4,5,6],[2,3,4,5,6,0,1],[4,5,6,0,1,2,3],[6,0,1,2,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,4,5,6,0],[3,4,5,6,0,1,2],[5,6,0,1,2,3,4],[0,1,2,3,4,5,6],[2,3,4,5,6,0,1],[4,5,6,0,1,2,3],[6,0,1,2,3,4,5]]» : Magma (Fin 7) where
  op := finOpTable "[[1,2,3,4,5,6,0],[3,4,5,6,0,1,2],[5,6,0,1,2,3,4],[0,1,2,3,4,5,6],[2,3,4,5,6,0,1],[4,5,6,0,1,2,3],[6,0,1,2,3,4,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,4,5,6,0],[3,4,5,6,0,1,2],[5,6,0,1,2,3,4],[0,1,2,3,4,5,6],[2,3,4,5,6,0,1],[4,5,6,0,1,2,3],[6,0,1,2,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2247, 2257, 2294] [47, 99, 151, 203, 261, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2240, 2244, 2246, 2254, 2256, 2264, 2301, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4283, 4314, 4343, 4380, 4585, 4598, 4608, 4635] :=
    ⟨Fin 7, «All4x4Tables [[1,2,3,4,5,6,0],[3,4,5,6,0,1,2],[5,6,0,1,2,3,4],[0,1,2,3,4,5,6],[2,3,4,5,6,0,1],[4,5,6,0,1,2,3],[6,0,1,2,3,4,5]]», Finite.of_fintype _, by decideFin!⟩
