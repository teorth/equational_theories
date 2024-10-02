
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 1, 1], [3, 1, 0, 2], [1, 1, 3, 1], [1, 1, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 1, 1], [3, 1, 0, 2], [1, 1, 3, 1], [1, 1, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 1, 1], [3, 1, 0, 2], [1, 1, 3, 1], [1, 1, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 1, 1], [3, 1, 0, 2], [1, 1, 3, 1], [1, 1, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1837, 1975, 2134, 4324, 4462, 4591] [40, 99, 151, 307, 359, 1020, 1629, 1833, 1834, 1835, 1838, 1840, 1841, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1932, 1934, 2036, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2135, 2137, 3253, 3456, 3659, 3862, 4065, 4270, 4272, 4314, 4320, 4343, 4381, 4382, 4383, 4385, 4386, 4388, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4583, 4590, 4606, 4608] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 1, 1], [3, 1, 0, 2], [1, 1, 3, 1], [1, 1, 1, 0]]», by decideFin!⟩
