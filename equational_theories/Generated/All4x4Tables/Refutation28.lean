
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,4,8,3,7,1,5,6],[3,1,5,7,8,6,0,2,4],[8,0,2,6,7,4,3,1,5],[1,5,6,3,0,8,2,4,7],[6,8,0,5,4,2,7,3,1],[7,3,1,4,6,5,8,0,2],[4,7,3,2,5,1,6,8,0],[5,6,8,1,2,0,4,7,3],[2,4,7,0,1,3,5,6,8]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,4,8,3,7,1,5,6],[3,1,5,7,8,6,0,2,4],[8,0,2,6,7,4,3,1,5],[1,5,6,3,0,8,2,4,7],[6,8,0,5,4,2,7,3,1],[7,3,1,4,6,5,8,0,2],[4,7,3,2,5,1,6,8,0],[5,6,8,1,2,0,4,7,3],[2,4,7,0,1,3,5,6,8]]» : Magma (Fin 9) where
  op := finOpTable "[[0,2,4,8,3,7,1,5,6],[3,1,5,7,8,6,0,2,4],[8,0,2,6,7,4,3,1,5],[1,5,6,3,0,8,2,4,7],[6,8,0,5,4,2,7,3,1],[7,3,1,4,6,5,8,0,2],[4,7,3,2,5,1,6,8,0],[5,6,8,1,2,0,4,7,3],[2,4,7,0,1,3,5,6,8]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,4,8,3,7,1,5,6],[3,1,5,7,8,6,0,2,4],[8,0,2,6,7,4,3,1,5],[1,5,6,3,0,8,2,4,7],[6,8,0,5,4,2,7,3,1],[7,3,1,4,6,5,8,0,2],[4,7,3,2,5,1,6,8,0],[5,6,8,1,2,0,4,7,3],[2,4,7,0,1,3,5,6,8]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [907, 1120] [429, 440, 464, 473, 477, 504, 513, 632, 643, 667, 676, 680, 707, 716, 836, 843, 1082, 1113, 1122, 1285, 1289, 1312, 1434, 1444, 1482, 1489, 1516, 1519, 1731, 2088, 2128, 2137, 2241, 2244, 2263, 2327, 2534, 2853, 2936, 2940, 2947, 3103, 3116, 3150, 3342, 3545, 3556, 3964, 4154, 4167, 4283, 4293, 4398, 4405, 4409, 4442, 4482, 4635] :=
    ⟨Fin 9, «All4x4Tables [[0,2,4,8,3,7,1,5,6],[3,1,5,7,8,6,0,2,4],[8,0,2,6,7,4,3,1,5],[1,5,6,3,0,8,2,4,7],[6,8,0,5,4,2,7,3,1],[7,3,1,4,6,5,8,0,2],[4,7,3,2,5,1,6,8,0],[5,6,8,1,2,0,4,7,3],[2,4,7,0,1,3,5,6,8]]», Finite.of_fintype _, by decideFin!⟩
