
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 2, 1], [3, 2, 3, 2], [0, 1, 2, 3], [2, 1, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 2, 1], [3, 2, 3, 2], [0, 1, 2, 3], [2, 1, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 2, 1], [3, 2, 3, 2], [0, 1, 2, 3], [2, 1, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 2, 1], [3, 2, 3, 2], [0, 1, 2, 3], [2, 1, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [203, 3115, 3684] [23, 211, 221, 231, 1629, 2238, 2441, 2644, 3058, 3139, 3152, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3759, 3824, 4065, 4590] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 2, 1], [3, 2, 3, 2], [0, 1, 2, 3], [2, 1, 0, 0]]», by decideFin!⟩
