
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 1, 1], [3, 3, 0, 0], [3, 1, 1, 1], [0, 2, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [3, 1, 1, 1], [0, 2, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 1, 1], [3, 3, 0, 0], [3, 1, 1, 1], [0, 2, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [3, 1, 1, 1], [0, 2, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2056, 3258, 4584] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2036, 2038, 2041, 2043, 2044, 2051, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [3, 1, 1, 1], [0, 2, 0, 0]]», by decideFin!⟩
