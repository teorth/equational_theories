
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 2 * x + 0 * y + 2 * x * y) % 3' (0, 150, 155, 158, 1831, 1836, 1846, 1856, 1866, 4064, 4066)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + 2 * x + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [156, 159, 4067] [359, 1426, 1629, 1833, 1834, 1835, 1838, 1840, 1841, 1848, 1850, 1851, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2035, 3253, 3456, 3862, 4066, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4283, 4380, 4635] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3», Finite.of_fintype _, by decideFin!⟩
