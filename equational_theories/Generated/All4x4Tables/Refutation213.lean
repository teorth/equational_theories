
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0],[1,2,0],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0],[1,2,0],[1,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[1,2,0],[1,2,0],[1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0],[1,2,0],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1539] [56, 99, 151, 203, 255, 411, 615, 620, 623, 630, 633, 640, 643, 667, 680, 707, 826, 833, 836, 843, 846, 870, 883, 917, 1020, 1223, 1427, 1429, 1435, 1445, 1479, 1519, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3865, 3868, 3871, 3878, 3917, 3927, 3951, 3964, 4066, 4068, 4071, 4074, 4120, 4127, 4130, 4167, 4268, 4270, 4273, 4283, 4290, 4314, 4380, 4583, 4585, 4588, 4598, 4605, 4629] :=
    ⟨Fin 3, «FinitePoly [[1,2,0],[1,2,0],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
