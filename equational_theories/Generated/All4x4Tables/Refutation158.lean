
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [3, 3, 3, 2], [0, 3, 3, 0], [2, 0, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [3, 3, 3, 2], [0, 3, 3, 0], [2, 0, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [3, 3, 3, 2], [0, 3, 3, 0], [2, 0, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [3, 3, 3, 2], [0, 3, 3, 0], [2, 0, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2125, 3511] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2036, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2127, 2128, 2134, 2135, 2137, 2238, 2441, 2644, 2847, 3050, 3253, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [3, 3, 3, 2], [0, 3, 3, 0], [2, 0, 1, 1]]», by decideFin!⟩
