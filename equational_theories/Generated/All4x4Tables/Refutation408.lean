
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [9, 101, 102, 152, 377, 429, 824, 827, 829, 1027, 1032, 1224, 1225, 1226, 1228, 1229, 1232, 1630, 1631, 1632, 2036, 2443, 2446, 2449, 2646, 2852, 3458, 3459, 3723, 3927, 4120, 4395, 4472, 4598] [4, 5, 28, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 103, 105, 107, 153, 166, 204, 206, 208, 209, 211, 212, 218, 219, 221, 222, 228, 229, 231, 256, 257, 258, 260, 261, 263, 264, 270, 271, 273, 274, 280, 281, 283, 309, 310, 312, 313, 315, 323, 325, 333, 335, 378, 384, 828, 830, 835, 1030, 1033, 1045, 1227, 1230, 1231, 1235, 1236, 1239, 1241, 1248, 1431, 1633, 1634, 1635, 1637, 1850, 2037, 2050, 2253, 2452, 2456, 2459, 2466, 2649, 2659, 2862, 2872, 3055, 3065, 3316, 3460, 3725, 3758, 3925, 4070, 4131, 4473, 4673] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]]», by decideFin!⟩
