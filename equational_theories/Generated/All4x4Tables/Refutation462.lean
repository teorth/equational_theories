
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
  ∃ (G : Type) (_ : Magma G), Facts G [1837, 1931, 2040, 2050, 2087, 4276, 4631] [8, 99, 151, 359, 411, 1020, 1223, 1629, 1834, 1838, 1847, 1850, 1861, 1888, 1897, 1922, 2036, 2037, 2038, 2041, 2043, 2044, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 3253, 3459, 3464, 3512, 3518, 3522, 3546, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 2, 1], [3, 3, 2, 2], [3, 0, 2, 1], [2, 0, 2, 0]]», by decideFin!⟩
