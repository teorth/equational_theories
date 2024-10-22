
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1929] [417, 429, 473, 477, 511, 614, 825, 833, 870, 872, 879, 883, 917, 1026, 1038, 1082, 1086, 1113, 1223, 1426, 1632, 1635, 1654, 1684, 1722, 1838, 1848, 1885, 1894, 2035, 2238, 2441, 2644, 2847, 3050, 3259, 3271, 3308, 3342, 3346, 3456, 3660, 3667, 3675, 3712, 3714, 3748, 3752, 3759, 3761, 3867, 3868, 3880, 3917, 3924, 3951, 3955, 3964, 4065, 4273, 4283, 4320, 4369, 4380, 4585, 4588, 4598, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[1,0,2,3],[2,3,0,1],[3,1,2,0]]», Finite.of_fintype _, by decideFin!⟩
