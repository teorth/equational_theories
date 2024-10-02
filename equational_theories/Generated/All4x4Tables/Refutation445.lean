
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [0, 0, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [0, 0, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [0, 0, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [0, 0, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [38, 3101] [2, 3, 8, 23, 39, 40, 43, 47, 99, 151, 203, 255, 312, 313, 315, 333, 335, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3152, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3472, 3474, 3475, 3481, 3482, 3484, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4065, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4380, 4587, 4588, 4590, 4591, 4605, 4606, 4608, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [0, 0, 0, 0]]», by decideFin!⟩
