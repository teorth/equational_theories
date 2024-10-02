
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 1, 3], [3, 0, 3, 0], [1, 0, 1, 3], [0, 3, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 1, 3], [3, 0, 3, 0], [1, 0, 1, 3], [0, 3, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 1, 3], [3, 0, 3, 0], [1, 0, 1, 3], [0, 3, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 1, 3], [3, 0, 3, 0], [1, 0, 1, 3], [0, 3, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3345, 3353, 4658] [43, 307, 359, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3346, 3352, 3355, 3456, 3659, 3862, 4065, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4343, 4368, 4380, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4683] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 1, 3], [3, 0, 3, 0], [1, 0, 1, 3], [0, 3, 0, 1]]», by decideFin!⟩
