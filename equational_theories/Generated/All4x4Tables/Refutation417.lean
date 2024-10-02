
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 0, 3], [3, 0, 1, 2], [0, 3, 2, 1], [1, 2, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 0, 3], [3, 0, 1, 2], [0, 3, 2, 1], [1, 2, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 0, 3], [3, 0, 1, 2], [0, 3, 2, 1], [1, 2, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 0, 3], [3, 0, 1, 2], [0, 3, 2, 1], [1, 2, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [452, 546, 562, 861, 949, 962, 1061, 1155, 1171, 1790, 1793, 1967, 1983, 2573, 2586, 3091, 3601, 3607, 4143, 4332, 4369] [8, 29, 31, 40, 43, 414, 419, 427, 436, 466, 477, 500, 511, 614, 818, 819, 820, 822, 823, 826, 832, 835, 836, 842, 843, 845, 869, 870, 873, 880, 882, 883, 906, 907, 909, 916, 919, 1023, 1028, 1036, 1045, 1075, 1086, 1109, 1120, 1223, 1426, 1635, 1637, 1645, 1647, 1691, 1695, 1718, 1722, 1835, 1840, 1848, 1857, 1887, 1898, 1921, 1932, 2035, 2238, 2444, 2447, 2459, 2466, 2494, 2507, 2530, 2543, 2644, 2847, 3103, 3105, 3112, 3116, 3139, 3143, 3150, 3152, 3253, 3462, 3464, 3481, 3509, 3511, 3545, 3549, 3659, 3862, 4081, 4083, 4090, 4154, 4158, 4165, 4167, 4270, 4275, 4283, 4320, 4380, 4588, 4590, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 0, 3], [3, 0, 1, 2], [0, 3, 2, 1], [1, 2, 3, 0]]», by decideFin!⟩
