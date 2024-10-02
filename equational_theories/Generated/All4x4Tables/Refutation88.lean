
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 3, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [0, 2, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 3, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [0, 2, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 3, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [0, 2, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 3, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [0, 2, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1238, 1239, 1248, 1251, 1252, 3318, 3319] [8, 99, 307, 359, 411, 614, 817, 1020, 1224, 1225, 1226, 1228, 1231, 1232, 1241, 1426, 1629, 1832, 2035, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4065, 4269, 4380, 4605] :=
    ⟨Fin 4, «FinitePoly [[1, 3, 0, 1], [2, 2, 1, 2], [2, 2, 2, 2], [0, 2, 3, 0]]», by decideFin!⟩
