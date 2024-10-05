
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 1 * y**2 + 2 * x + 2 * y + 1 * x * y) % 3' (0, 3252, 3305, 4590)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly y² + 2 * x + 2 * y + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => y*y + 2 * x + 2 * y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly y² + 2 * x + 2 * y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [4591] [411, 1020, 1223, 1832, 3318, 3319, 3862, 4065] :=
    ⟨Fin 3, «FinitePoly y² + 2 * x + 2 * y + x * y % 3», by decideFin!⟩
