
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 4270, 4272, 4390, 4442, 4443, 4471, 4484, 4497, 4498, 4499, 4592, 4629] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4368, 4373, 4382, 4383, 4385, 4386, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4444, 4445, 4472, 4473, 4479, 4480, 4547, 4571, 4584, 4585, 4587, 4588, 4598, 4599, 4605, 4606, 4630, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]», by decideFin!⟩
