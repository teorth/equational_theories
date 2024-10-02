
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 1, 1], [3, 0, 3, 2], [2, 2, 2, 2], [2, 0, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 1, 1], [3, 0, 3, 2], [2, 2, 2, 2], [2, 0, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 1, 1], [3, 0, 3, 2], [2, 2, 2, 2], [2, 0, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 1, 1], [3, 0, 3, 2], [2, 2, 2, 2], [2, 0, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1427, 1428, 1431, 1634, 1638, 3867, 4269, 4591] [23, 151, 203, 307, 1429, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1452, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 1630, 1631, 1632, 1635, 1637, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1731, 1832, 2238, 2441, 3050, 3253, 3456, 3864, 3865, 3868, 3870, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065, 4314] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 1, 1], [3, 0, 3, 2], [2, 2, 2, 2], [2, 0, 0, 1]]», by decideFin!⟩
