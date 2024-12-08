
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,0],[1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,2],[1,0,0],[1,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[1,0,0],[1,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,2],[1,0,0],[1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2808, 3278, 3306, 3456] [417, 427, 440, 477, 504, 511, 614, 825, 833, 835, 842, 846, 870, 872, 879, 883, 906, 917, 1023, 1028, 1038, 1049, 1082, 1109, 1223, 1426, 1629, 1838, 1857, 1887, 1894, 1925, 2088, 2101, 2124, 2128, 2238, 2441, 2652, 2662, 2697, 2744, 2847, 3050, 3256, 3259, 3261, 3271, 3308, 3315, 3342, 3462, 3464, 3509, 3511, 3518, 3659, 3862, 4065, 4283, 4320, 4585, 4590] :=
    ⟨Fin 3, «All4x4Tables [[0,1,2],[1,0,0],[1,0,1]]», Finite.of_fintype _, by decideFin!⟩
