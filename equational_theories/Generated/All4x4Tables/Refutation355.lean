
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 3, 1], [3, 2, 3, 1], [1, 2, 3, 1], [2, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 3, 1], [3, 2, 3, 1], [1, 2, 3, 1], [2, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 3, 1], [3, 2, 3, 1], [1, 2, 3, 1], [2, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 3, 1], [3, 2, 3, 1], [1, 2, 3, 1], [2, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [47, 359, 614, 817, 1426, 3918, 4121] [48, 49, 50, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 307, 360, 361, 362, 364, 365, 367, 375, 377, 378, 385, 411, 616, 822, 842, 1020, 1223, 1427, 1428, 1429, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1452, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 1629, 1832, 2035, 2847, 3253, 3456, 3659, 3877, 3915, 4118, 4127, 4131, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 3, 1], [3, 2, 3, 1], [1, 2, 3, 1], [2, 2, 3, 1]]», by decideFin!⟩
