
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1853, 1863, 3322, 4269] [8, 23, 99, 151, 203, 307, 359, 411, 817, 1020, 1223, 1426, 1629, 1835, 1837, 1861, 2238, 2441, 3050, 3256, 3258, 3261, 3309, 3315, 3318, 3456, 3543, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4270, 4284, 4583, 4598] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]», by decideFin!⟩
