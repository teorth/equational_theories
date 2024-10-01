
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 1], [2, 1, 0, 1], [2, 1, 1, 1], [2, 3, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 1], [2, 1, 0, 1], [2, 1, 1, 1], [2, 3, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 1], [2, 1, 0, 1], [2, 1, 1, 1], [2, 3, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 1], [2, 1, 0, 1], [2, 1, 1, 1], [2, 3, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [107, 1041, 1634, 1637, 3662, 4341] [23, 100, 101, 102, 105, 108, 114, 115, 117, 118, 124, 125, 127, 1122, 1225, 1226, 1251, 1252, 1278, 1312, 1325, 1426, 1630, 1631, 1632, 1635, 1638, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1731, 2441, 3050, 3253, 3456, 3684, 3712, 3715, 3722, 3759, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 1], [2, 1, 0, 1], [2, 1, 1, 1], [2, 3, 0, 3]]», by decideFin!⟩
