
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 1, 3], [3, 0, 0, 2], [0, 2, 3, 1], [1, 3, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 1, 3], [3, 0, 0, 2], [0, 2, 3, 1], [1, 3, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 1, 3], [3, 0, 0, 2], [0, 2, 3, 1], [1, 3, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 1, 3], [3, 0, 0, 2], [0, 2, 3, 1], [1, 3, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 1838, 1850, 1861, 1897, 1922, 4068, 4073, 4127, 4131, 4293, 4321] [23, 47, 817, 1020, 1426, 1629, 1833, 1834, 1835, 1837, 1840, 1841, 1847, 1848, 1851, 1857, 1858, 1860, 1873, 1884, 1885, 1887, 1888, 1894, 1895, 1898, 1921, 1924, 1925, 1931, 1932, 1934, 2035, 2441, 2644, 3050, 3456, 3659, 4071, 4118, 4120, 4135, 4276, 4343, 4380, 4585, 4598] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 1, 3], [3, 0, 0, 2], [0, 2, 3, 1], [1, 3, 2, 0]]», by decideFin!⟩
