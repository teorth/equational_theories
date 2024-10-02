
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 4442, 4443, 4484, 4629] [8, 23, 40, 43, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4275, 4283, 4290, 4291, 4293, 4321, 4396, 4398, 4399, 4405, 4406, 4435, 4436, 4444, 4630, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[1, 3, 1, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]», by decideFin!⟩
