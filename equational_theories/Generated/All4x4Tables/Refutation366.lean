
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 3, 1], [3, 3, 3, 0], [3, 0, 0, 0], [2, 0, 1, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 3, 1], [3, 3, 3, 0], [3, 0, 0, 0], [2, 0, 1, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 3, 1], [3, 3, 3, 0], [3, 0, 0, 0], [2, 0, 1, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 3, 1], [3, 3, 3, 0], [3, 0, 0, 0], [2, 0, 1, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1833, 2035, 3457] [3, 8, 23, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1837, 1838, 1847, 1848, 2036, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2098, 2100, 2101, 2124, 2125, 2127, 2128, 2134, 2135, 2137, 2238, 2441, 2644, 2847, 3050, 3253, 3522, 3659, 3862, 4065, 4268, 4380] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 3, 1], [3, 3, 3, 0], [3, 0, 0, 0], [2, 0, 1, 2]]», by decideFin!⟩
