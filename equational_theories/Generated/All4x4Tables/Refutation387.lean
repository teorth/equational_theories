
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4301, 4312, 4331, 4429, 4430, 4466, 4467, 4487, 4495, 4646] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4271, 4278, 4287, 4300, 4315, 4358, 4362, 4364, 4369, 4381, 4388, 4396, 4408, 4433, 4445, 4470, 4482, 4583, 4590, 4598, 4599, 4605, 4606, 4608, 4677] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3]]», by decideFin!⟩
