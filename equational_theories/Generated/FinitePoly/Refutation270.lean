
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 1 * x + 2 * y + 4 * x * y) % 5' (0, 202, 204, 2237, 2239, 2242, 2245, 2248, 2440, 2458)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + x + 2 * y + 4 * x * y

/-! The facts -/
theorem «Facts from FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [205, 2238, 2459] [4065] :=
    ⟨Fin 5, «FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5», by decideFin!⟩
