
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3334, 3388, 3414, 4135, 4143, 4146, 4307] [8, 23, 43, 307, 359, 411, 1020, 1629, 1832, 2441, 3050, 3254, 3255, 3256, 3258, 3259, 3262, 3268, 3269, 3272, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3342, 3343, 3345, 3352, 3355, 3456, 3659, 3862, 4154, 4158, 4283, 4380, 4635] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 2, 3], [2, 3, 3, 2], [3, 2, 2, 3], [2, 3, 3, 2]]», by decideFin!⟩
