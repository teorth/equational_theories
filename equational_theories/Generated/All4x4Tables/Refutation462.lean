
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1837, 1931, 2040, 2050, 2087, 4276, 4584] [8, 99, 151, 359, 411, 1020, 1223, 1629, 1833, 1834, 1835, 1838, 1840, 1841, 1847, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1932, 1934, 2036, 2037, 2038, 2041, 2043, 2044, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 3253, 3457, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]]», by decideFin!⟩
