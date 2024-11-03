
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,2,0],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[1,2,0],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[1,2,0],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[1,2,0],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [151, 1036, 1050, 1240, 1243, 1263] [53, 107, 159, 203, 255, 411, 614, 817, 1022, 1023, 1028, 1029, 1035, 1039, 1046, 1225, 1229, 1249, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4293, 4314, 4398, 4399, 4433, 4435, 4436, 4470, 4472, 4473, 4583, 4584, 4585, 4590, 4598, 4599, 4606, 4608, 4629, 4636] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[1,2,0],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
