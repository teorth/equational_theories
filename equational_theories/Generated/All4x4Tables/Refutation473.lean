
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 1], [3, 2, 1, 0], [2, 2, 2, 2], [2, 2, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 1], [3, 2, 1, 0], [2, 2, 2, 2], [2, 2, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 1], [3, 2, 1, 0], [2, 2, 2, 2], [2, 2, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 1], [3, 2, 1, 0], [2, 2, 2, 2], [2, 2, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [107, 108, 847, 1250, 1253, 1254, 1255, 1263, 1832, 4591] [835, 1020, 1238, 1239, 1241, 1833, 1834, 1835, 1837, 1838, 1840, 1841, 1847, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 3870, 3878, 3915] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 1], [3, 2, 1, 0], [2, 2, 2, 2], [2, 2, 3, 2]]», by decideFin!⟩
