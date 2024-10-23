
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(4 * x**2 + 4 * y**2 + 0 * x + 4 * y + 2 * x * y) % 5' (0, 150, 158)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 4 * x² + 4 * y² + 4 * y + 2 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 4 * x*x + 4 * y*y + 4 * y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 4 * x² + 4 * y² + 4 * y + 2 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [159] [47, 99, 154, 157, 160, 167, 169, 170, 176, 177, 179, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 5, «FinitePoly 4 * x² + 4 * y² + 4 * y + 2 * x * y % 5», Finite.of_fintype _, by decideFin!⟩
