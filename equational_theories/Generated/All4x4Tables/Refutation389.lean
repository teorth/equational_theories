
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]» : Magma (Fin 4) where
  op := finOpTable "[[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1032, 1453, 2260, 2460, 2650, 3317, 3320] [50, 101, 377, 378, 416, 417, 419, 420, 619, 620, 622, 623, 819, 820, 823, 1021, 1224, 1228, 1232, 1428, 1429, 1630, 1631, 1833, 1837, 2036, 2243, 2246, 2443, 2646, 2660, 2852, 3056, 3068, 3255, 3256, 3457, 3458, 3660, 3724, 3725, 3864, 3918, 3925, 3928, 4268, 4598] :=
    ⟨Fin 4, «All4x4Tables [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]», Finite.of_fintype _, by decideFin!⟩
