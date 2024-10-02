
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 3], [3, 3, 3, 3], [3, 3, 1, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 3], [3, 3, 3, 3], [3, 3, 1, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 3], [3, 3, 3, 3], [3, 3, 1, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 3], [3, 3, 3, 3], [3, 3, 1, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4451] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4270, 4272, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4343, 4396, 4398, 4399, 4405, 4406, 4408, 4470, 4472, 4473, 4479, 4480, 4482] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 3], [3, 3, 3, 3], [3, 3, 1, 3], [3, 3, 3, 3]]», by decideFin!⟩
