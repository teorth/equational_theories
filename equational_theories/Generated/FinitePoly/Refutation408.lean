
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 2 * y**2 + 2 * x + 1 * y + 0 * x * y) % 5' (0, 3049, 3055, 3067, 3078, 3090)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * y² + 2 * x + y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 2 * y*y + 2 * x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * y² + 2 * x + y % 5» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3091] [1426, 1629, 1832, 2238, 2441, 3053, 3058, 3066, 3075, 3253, 3456, 4065, 4585, 4598] :=
    ⟨Fin 5, «FinitePoly 2 * y² + 2 * x + y % 5», Finite.of_fintype _, by decideFin!⟩
