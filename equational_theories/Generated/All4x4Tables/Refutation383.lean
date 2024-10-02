
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 3, 3], [3, 1, 2, 0], [0, 2, 1, 3], [3, 1, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 3, 3], [3, 1, 2, 0], [0, 2, 1, 3], [3, 1, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 3, 3], [3, 1, 2, 0], [0, 2, 1, 3], [3, 1, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 3, 3], [3, 1, 2, 0], [0, 2, 1, 3], [3, 1, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [614, 817, 1488, 1857, 2060, 2300, 2327, 2652, 2872, 3353, 4065, 4473] [11, 16, 414, 419, 429, 436, 440, 466, 473, 500, 513, 622, 630, 639, 643, 676, 703, 820, 823, 835, 842, 846, 872, 906, 1028, 1036, 1038, 1045, 1049, 1075, 1082, 1109, 1122, 1231, 1248, 1312, 1325, 1429, 1434, 1481, 1647, 1682, 1731, 1835, 1840, 1850, 1861, 1887, 1894, 1921, 1934, 2038, 2090, 2137, 2246, 2263, 2449, 2459, 2496, 2699, 2706, 2909, 2936, 3256, 3261, 3271, 3278, 3306, 3315, 3346, 3481, 3549, 3662, 3677, 3721, 3722, 3725, 3759, 3870, 3880, 3887, 3928, 3955, 3962, 4068, 4073, 4131, 4270, 4275, 4320, 4442] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 3, 3], [3, 1, 2, 0], [0, 2, 1, 3], [3, 1, 2, 0]]», by decideFin!⟩
