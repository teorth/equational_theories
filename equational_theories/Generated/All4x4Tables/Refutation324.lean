
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 1], [2, 2, 1, 2], [0, 0, 2, 1], [0, 2, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 1], [2, 2, 1, 2], [0, 0, 2, 1], [0, 2, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 1], [2, 2, 1, 2], [0, 0, 2, 1], [0, 2, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 1], [2, 2, 1, 2], [0, 0, 2, 1], [0, 2, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [643, 861, 1252] [8, 411, 617, 620, 622, 630, 632, 639, 680, 707, 714, 716, 820, 823, 835, 842, 1020, 1226, 1229, 1231, 1239, 1241, 1248, 1289, 1316, 1323, 1325, 1832, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3659, 3862, 4270] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 1], [2, 2, 1, 2], [0, 0, 2, 1], [0, 2, 3, 0]]», by decideFin!⟩
