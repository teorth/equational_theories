
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [156, 159, 1832, 4067] [43, 152, 153, 166, 1426, 1629, 1834, 1840, 1850, 1860, 1884, 1887, 1894, 1897, 1921, 1924, 1931, 1934, 2035, 3253, 3456, 3862, 4070, 4073, 4080, 4083, 4090, 4093, 4118, 4121, 4128, 4131, 4155, 4158, 4165, 4283, 4380, 4635] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3», by decideFin!⟩
