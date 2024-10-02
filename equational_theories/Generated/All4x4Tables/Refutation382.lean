
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [0, 3, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [0, 3, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [0, 3, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [0, 3, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1020, 2134, 4591] [151, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1832, 2036, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2135, 2137, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3862, 4065, 4606] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [0, 3, 1, 0]]», by decideFin!⟩
