
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(4 * x**2 + 4 * y**2 + 3 * x + 2 * y + 3 * x * y) % 5' (0, 98, 103, 1019, 1037, 1222, 1227, 1237, 1247, 1257)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 4 * x² + 4 * y² + 3 * x + 2 * y + 3 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 4 * x*x + 4 * y*y + 3 * x + 2 * y + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 4 * x² + 4 * y² + 3 * x + 2 * y + 3 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [104, 1038] [3253] :=
    ⟨Fin 5, «FinitePoly 4 * x² + 4 * y² + 3 * x + 2 * y + 3 * x * y % 5», Finite.of_fintype _, by decideFin!⟩
