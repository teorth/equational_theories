
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,1,4,0,2],[4,3,2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,1,4,0,2],[4,3,2,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,1,4,0,2],[4,3,2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,1,4,0,2],[4,3,2,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [543, 928, 952, 978, 1117, 1152, 1670, 1673, 1740, 1774, 1876, 1964, 2474, 2482, 2538, 2552, 2576, 2602, 3398, 3737, 3823, 4007] [417, 429, 464, 473, 477, 511, 614, 825, 833, 872, 879, 883, 919, 1026, 1038, 1073, 1082, 1086, 1120, 1223, 1426, 1632, 1654, 1682, 1684, 1695, 1722, 1838, 1850, 1885, 1894, 1898, 1932, 2035, 2238, 2449, 2457, 2496, 2503, 2507, 2543, 2644, 2847, 3050, 3259, 3271, 3308, 3342, 3346, 3456, 3667, 3675, 3712, 3748, 3752, 3759, 3868, 3880, 3917, 3951, 3955, 3964, 4065, 4273, 4283, 4320, 4380, 4585, 4605, 4635] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,1,4,0,2],[4,3,2,1,0]]», by decideFin!⟩
