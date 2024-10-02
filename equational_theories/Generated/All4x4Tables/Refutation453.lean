
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3909, 4368, 4373] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3865, 3868, 3871, 3878, 3881, 3888, 3892, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4055, 4065, 4258, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 0, 3]]», by decideFin!⟩
