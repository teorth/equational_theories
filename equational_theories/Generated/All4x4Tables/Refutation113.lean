
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[1,0,0],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[1,0,0],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[1,0,0],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[1,0,0],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [861] [43, 99, 359, 411, 614, 819, 832, 835, 836, 842, 843, 845, 870, 872, 879, 883, 906, 917, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3870, 3880, 3887, 3928, 3955, 3962, 4066, 4067, 4070, 4073, 4118, 4120, 4127, 4269, 4273, 4290, 4314, 4583, 4584, 4585, 4598] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[1,0,0],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
