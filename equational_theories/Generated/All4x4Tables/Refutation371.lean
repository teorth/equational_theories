
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [3, 2, 1, 0], [1, 0, 1, 1], [1, 0, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [3, 2, 1, 0], [1, 0, 1, 1], [1, 0, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [3, 2, 1, 0], [1, 0, 1, 1], [1, 0, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [3, 2, 1, 0], [1, 0, 1, 1], [1, 0, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 153, 166, 1691, 1705, 2090, 2169, 3258, 3306, 3353, 3877, 3952, 3955, 3962, 4606] [3, 8, 23, 39, 47, 99, 156, 159, 169, 176, 179, 203, 255, 307, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1644, 1647, 1654, 1657, 1681, 1697, 1718, 1721, 1728, 1731, 1832, 2037, 2040, 2043, 2060, 2063, 2097, 2100, 2134, 2137, 2165, 2238, 2441, 2644, 2847, 3050, 3255, 3261, 3268, 3271, 3278, 3281, 3309, 3316, 3319, 3343, 3346, 3456, 3659, 3864, 3867, 3870, 3880, 3887, 3890, 3915, 3918, 3925, 3928, 4055, 4065, 4258, 4269, 4272, 4275, 4284, 4291, 4320, 4380, 4584, 4587, 4590, 4599, 4635] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [3, 2, 1, 0], [1, 0, 1, 1], [1, 0, 1, 0]]», by decideFin!⟩
