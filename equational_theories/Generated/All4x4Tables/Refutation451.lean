
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [455, 508, 914, 1137, 1929, 1996] [43, 417, 429, 464, 473, 477, 511, 543, 614, 825, 833, 870, 872, 879, 883, 917, 919, 1026, 1038, 1073, 1082, 1086, 1113, 1120, 1223, 1426, 1632, 1635, 1645, 1654, 1658, 1682, 1684, 1695, 1722, 1729, 1838, 1848, 1850, 1885, 1894, 1898, 1932, 2035, 2051, 2053, 2060, 2064, 2088, 2090, 2097, 2101, 2124, 2128, 2135, 2137, 2238, 2441, 2644, 2847, 3050, 3259, 3271, 3308, 3342, 3346, 3398, 3456, 3667, 3675, 3712, 3714, 3748, 3752, 3759, 3761, 3868, 3880, 3917, 3924, 3951, 3955, 3964, 4065, 4098, 4118, 4120, 4127, 4131, 4154, 4158, 4165, 4167, 4273, 4283, 4320, 4369, 4380, 4585, 4588, 4598, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]», by decideFin!⟩
