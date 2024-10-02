
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 1, 3], [3, 1, 1, 3], [1, 3, 0, 1], [3, 1, 1, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 1, 3], [3, 1, 1, 3], [1, 3, 0, 1], [3, 1, 1, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 1, 3], [3, 1, 1, 3], [1, 3, 0, 1], [3, 1, 1, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 1, 3], [3, 1, 1, 3], [1, 3, 0, 1], [3, 1, 1, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4428, 4587, 4590, 4682] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4273, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4321, 4343, 4368, 4373, 4381, 4383, 4386, 4398, 4405, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4539, 4547, 4571, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 1, 3], [3, 1, 1, 3], [1, 3, 0, 1], [3, 1, 1, 3]]», by decideFin!⟩
