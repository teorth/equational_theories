
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 1, 1], [3, 3, 0, 0], [2, 2, 0, 0], [3, 3, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [2, 2, 0, 0], [3, 3, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 1, 1], [3, 3, 0, 0], [2, 2, 0, 0], [3, 3, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [2, 2, 0, 0], [3, 3, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [162, 3330, 4134] [23, 152, 154, 157, 160, 166, 167, 169, 170, 176, 177, 179, 203, 307, 1426, 1630, 1632, 1635, 1638, 1645, 1648, 1655, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1731, 2035, 2238, 2441, 3050, 3456, 4070, 4118, 4584] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 1, 1], [3, 3, 0, 0], [2, 2, 0, 0], [3, 3, 1, 1]]», by decideFin!⟩
