
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 3], [3, 0, 3, 3], [0, 3, 0, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 3], [3, 0, 3, 3], [0, 3, 0, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 3], [3, 0, 3, 3], [0, 3, 0, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 3], [3, 0, 3, 3], [0, 3, 0, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [43, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 4291, 4293, 4321, 4358, 4399, 4406, 4436, 4443, 4544, 4629, 4636, 4658] [2, 3, 8, 23, 38, 39, 40, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3715, 3758, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4284, 4290, 4314, 4320, 4343, 4368, 4373, 4381, 4382, 4383, 4385, 4386, 4388, 4396, 4408, 4433, 4445, 4470, 4472, 4473, 4479, 4480, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 3], [3, 0, 3, 3], [0, 3, 0, 3], [3, 3, 3, 3]]», by decideFin!⟩
