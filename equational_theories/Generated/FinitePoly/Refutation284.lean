
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 1 * y**2 + 1 * x + 1 * y + 0 * x * y) % 3' (0, 150, 4275, 4379, 4388, 4590)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + y² + x + y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + y*y + x + y

/-! The facts -/
theorem «Facts from FinitePoly 2 * x² + y² + x + y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [151, 4389, 4591] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 152, 153, 154, 156, 157, 159, 160, 166, 167, 169, 170, 176, 177, 179, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4381, 4382, 4383, 4385, 4386, 4388, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 3, «FinitePoly 2 * x² + y² + x + y % 3», by decideFin!⟩
