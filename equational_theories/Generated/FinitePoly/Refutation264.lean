
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 1 * x + 0 * y + 2 * x * y) % 3' (0, 816, 831, 845, 1019, 1034, 1048, 4064, 4130, 4597, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [832, 846, 1035, 1049] [47, 99, 151, 203, 255, 359, 411, 614, 822, 1022, 1025, 1028, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4380] :=
    ⟨Fin 3, «FinitePoly x + 2 * x * y % 3», Finite.of_fintype _, by decideFin!⟩
