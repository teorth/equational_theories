
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(3 * x**2 + 1 * y**2 + 1 * x + 1 * y + 0 * x * y) % 4' (0, 3252, 3260, 3270, 3277, 3305, 3318, 3333, 3345, 3352, 3387, 3413, 4064, 4067, 4070, 4072, 4117, 4119, 4126, 4130, 4134, 4142, 4145, 4274, 4306, 4319, 4361, 4584, 4597, 4655, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 3 * x² + y² + x + y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 3 * x*x + y*y + x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 3 * x² + y² + x + y % 4» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3388] [411, 1020, 1223, 1629, 1832, 2035, 3862] :=
    ⟨Fin 4, «FinitePoly 3 * x² + y² + x + y % 4», Finite.of_fintype _, by decideFin!⟩
