
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 1, 1], [3, 3, 3, 2], [0, 1, 2, 3], [2, 0, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 1, 1], [3, 3, 3, 2], [0, 1, 2, 3], [2, 0, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 1, 1], [3, 3, 3, 2], [0, 1, 2, 3], [2, 0, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 1, 1], [3, 3, 3, 2], [0, 1, 2, 3], [2, 0, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [231, 2044, 3152, 3262, 4276] [3, 8, 23, 47, 99, 151, 209, 212, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2036, 2037, 2038, 2040, 2041, 2043, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 2238, 2441, 2644, 2847, 3053, 3056, 3058, 3066, 3075, 3079, 3254, 3255, 3256, 3258, 3259, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3459, 3464, 3465, 3518, 3522, 3659, 3862, 4065, 4380, 4585] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 1, 1], [3, 3, 3, 2], [0, 1, 2, 3], [2, 0, 0, 0]]», by decideFin!⟩
