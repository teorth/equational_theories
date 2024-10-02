
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 3, 3], [3, 3, 2, 2], [0, 0, 1, 1], [1, 1, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 3, 3], [3, 3, 2, 2], [0, 0, 1, 1], [1, 1, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 3, 3], [3, 3, 2, 2], [0, 0, 1, 1], [1, 1, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 3, 3], [3, 3, 2, 2], [0, 0, 1, 1], [1, 1, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1663, 1874, 2489, 3527, 4357] [24, 25, 28, 29, 31, 151, 203, 307, 1426, 1634, 1635, 1637, 1638, 1644, 1645, 1647, 1648, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1731, 1834, 1835, 1840, 1841, 1847, 1848, 1857, 1858, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2238, 2442, 2444, 2447, 2450, 2456, 2459, 2466, 2469, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 3253, 4066, 4067, 4070, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4121, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 3, 3], [3, 3, 2, 2], [0, 0, 1, 1], [1, 1, 0, 0]]», by decideFin!⟩
