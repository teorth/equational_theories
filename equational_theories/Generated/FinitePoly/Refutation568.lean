
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 1 * x + 1 * y + 0 * x * y) % 3' (0, 42, 46, 55, 65, 72, 74, 98, 107, 117, 124, 126, 150, 159, 169, 176, 178, 202, 211, 221, 228, 230, 254, 263, 273, 280, 282, 4275, 4282, 4289, 4319, 4357, 4361, 4363, 4368, 4379, 4388, 4395, 4397, 4404, 4432, 4434, 4441, 4472, 4479, 4481, 4511, 4514, 4524, 4530, 4540, 4543, 4590, 4597, 4604, 4634, 4672, 4676, 4678, 4683)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x + y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x + y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [43, 56, 66, 73, 75, 108, 118, 125, 127, 160, 170, 177, 179, 212, 222, 229, 231, 264, 274, 281, 283, 4389] [50, 53, 55, 63, 65, 72, 102, 105, 107, 115, 117, 124, 154, 157, 159, 167, 169, 176, 206, 209, 211, 219, 221, 228, 258, 261, 263, 271, 273, 280, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4284, 4291, 4293, 4314, 4321, 4343, 4399, 4406, 4408, 4436, 4443, 4445, 4470, 4472, 4479, 4583, 4584, 4585, 4587, 4588, 4590, 4599, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly x + y % 3», Finite.of_fintype _, by decideFin!⟩
