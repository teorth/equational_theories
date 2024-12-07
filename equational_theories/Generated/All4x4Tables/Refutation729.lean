
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,4,3,2],[1,1,1,1,1,1],[4,3,2,5,0,3],[2,4,0,3,5,4],[5,0,3,2,4,0],[3,5,4,0,2,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,5,4,3,2],[1,1,1,1,1,1],[4,3,2,5,0,3],[2,4,0,3,5,4],[5,0,3,2,4,0],[3,5,4,0,2,5]]» : Magma (Fin 6) where
  op := finOpTable "[[0,2,5,4,3,2],[1,1,1,1,1,1],[4,3,2,5,0,3],[2,4,0,3,5,4],[5,0,3,2,4,0],[3,5,4,0,2,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,5,4,3,2],[1,1,1,1,1,1],[4,3,2,5,0,3],[2,4,0,3,5,4],[5,0,3,2,4,0],[3,5,4,0,2,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [261, 2054, 2061, 2450, 2873] [156, 159, 160, 205, 206, 208, 209, 211, 263, 323, 1427, 1428, 1429, 1431, 1432, 1434, 1435, 1441, 1444, 1445, 1451, 1454, 1455, 1630, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1645, 1848, 2036, 2043, 2044, 2053, 2060, 2256, 2457, 2459, 2646, 2650, 2669, 2672, 2852, 2856, 2863, 2865, 2875, 3066, 3254, 3255, 3256, 3259, 3308, 3315, 3316, 3318, 3457, 3458, 3459, 3462, 3511, 3518, 3519, 3521, 4268, 4314, 4598, 4656] :=
    ⟨Fin 6, «All4x4Tables [[0,2,5,4,3,2],[1,1,1,1,1,1],[4,3,2,5,0,3],[2,4,0,3,5,4],[5,0,3,2,4,0],[3,5,4,0,2,5]]», Finite.of_fintype _, by decideFin!⟩
