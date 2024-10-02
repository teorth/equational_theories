
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 1, 1], [3, 1, 3, 2], [1, 2, 0, 3], [0, 3, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 1, 1], [3, 1, 3, 2], [1, 2, 0, 3], [0, 3, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 1, 1], [3, 1, 3, 2], [1, 2, 0, 3], [0, 3, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 1, 1], [3, 1, 3, 2], [1, 2, 0, 3], [0, 3, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [108, 3079, 3106, 3149, 4591, 4658] [2, 3, 8, 23, 38, 39, 40, 43, 47, 100, 101, 102, 104, 105, 107, 114, 115, 117, 118, 124, 125, 127, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3051, 3052, 3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3102, 3103, 3105, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3150, 3152, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 1, 1], [3, 1, 3, 2], [1, 2, 0, 3], [0, 3, 2, 0]]», by decideFin!⟩
