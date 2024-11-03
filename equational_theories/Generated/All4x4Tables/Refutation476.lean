
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,2,0,1],[2,2,3,0],[3,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,2,0,1],[2,2,3,0],[3,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,2,0,1],[2,2,3,0],[3,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,2,0,1],[2,2,3,0],[3,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [630, 640] [55, 99, 151, 203, 255, 411, 615, 616, 619, 620, 622, 623, 629, 632, 633, 639, 642, 669, 676, 680, 707, 819, 825, 826, 832, 833, 835, 836, 842, 843, 845, 846, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,2,0,1],[2,2,3,0],[3,0,3,1]]», Finite.of_fintype _, by decideFin!⟩
