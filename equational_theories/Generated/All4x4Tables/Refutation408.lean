
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
  ∃ (G : Type) (_ : Magma G), Facts G [9, 23, 48, 50, 101, 102, 152, 203, 255, 307, 377, 425, 429, 628, 821, 824, 827, 829, 1023, 1027, 1032, 1224, 1226, 1228, 1229, 1232, 1427, 1429, 1630, 1631, 1632, 1833, 1837, 1838, 2036, 2249, 2443, 2446, 2449, 2646, 2852, 3257, 3318, 3458, 3459, 3715, 3723, 3864, 3927, 4120, 4395, 4470, 4472, 4598] [52, 103, 105, 107, 153, 208, 309, 378, 828, 830, 835, 1030, 1033, 1045, 1227, 1230, 1231, 1235, 1236, 1239, 1241, 1248, 1431, 1633, 1634, 1635, 1637, 1850, 2037, 2253, 2452, 2456, 2459, 2466, 2649, 2862, 3316, 3460, 3725, 3925, 4131, 4473, 4673] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 1], [2, 0, 2, 2], [3, 2, 3, 3]]», by decideFin!⟩
