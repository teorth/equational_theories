
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 1, 1], [3, 1, 1, 1], [1, 3, 3, 3], [1, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 1, 1], [3, 1, 1, 1], [1, 3, 3, 3], [1, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 1, 1], [3, 1, 1, 1], [1, 3, 3, 3], [1, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 1, 1], [3, 1, 1, 1], [1, 3, 3, 3], [1, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4521] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4381, 4382, 4385, 4386, 4388, 4396, 4398, 4405, 4406, 4408, 4433, 4435, 4442, 4443, 4445, 4470, 4472, 4479, 4480, 4482, 4583, 4584, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 1, 1], [3, 1, 1, 1], [1, 3, 3, 3], [1, 3, 3, 3]]», by decideFin!⟩
