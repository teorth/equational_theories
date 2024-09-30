
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 1 * y**2 + 3 * x + 2 * y + 3 * x * y) % 5' (0, 39, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3723, 4269, 4292, 4340, 4589, 4621, 4635)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => x*x + y*y + 3 * x + 2 * y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [3700, 4293, 4636] [307, 3253, 3664, 3668, 3674, 3678, 3721, 3725, 4065, 4272, 4276, 4343] :=
    ⟨Fin 5, «FinitePoly x² + y² + 3 * x + 2 * y + 3 * x * y % 5», by decideFin!⟩
