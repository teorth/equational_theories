
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 1], [3, 1, 1, 1], [3, 1, 0, 1], [3, 1, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 1], [3, 1, 1, 1], [3, 1, 0, 1], [3, 1, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 1], [3, 1, 1, 1], [3, 1, 0, 1], [3, 1, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 1], [3, 1, 1, 1], [3, 1, 0, 1], [3, 1, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4328, 4599, 4677] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4273, 4275, 4276, 4284, 4290, 4314, 4320, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4605, 4608, 4629, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 1], [3, 1, 1, 1], [3, 1, 0, 1], [3, 1, 1, 1]]», by decideFin!⟩
