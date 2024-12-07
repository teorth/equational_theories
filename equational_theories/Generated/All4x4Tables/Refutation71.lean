
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,2,0],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,2],[0,2,0],[0,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,2,0],[0,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,2],[0,2,0],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2296, 2351, 2372, 2496, 2609, 4389, 4473] [47, 99, 159, 211, 273, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2253, 2300, 2303, 2443, 2456, 2466, 2506, 2530, 2533, 2540, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4291, 4314, 4320, 4396, 4398, 4399, 4406, 4408, 4433, 4435, 4442, 4445, 4470, 4472, 4480, 4482, 4584, 4585, 4587, 4590, 4598, 4599, 4606, 4635] :=
    ⟨Fin 3, «All4x4Tables [[0,1,2],[0,2,0],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
