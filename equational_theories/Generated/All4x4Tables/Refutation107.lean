
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[1,0,0],[2,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[1,0,0],[2,0,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[1,0,0],[2,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[1,0,0],[2,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [455, 647, 655, 1061] [466, 473, 477, 504, 511, 513, 667, 669, 676, 680, 707, 870, 872, 879, 883, 906, 917, 1075, 1082, 1086, 1109, 1113, 1122, 1276, 1278, 1285, 1426, 1629, 1838, 1840, 1848, 1850, 1885, 1887, 1894, 1921, 1925, 2035, 2238, 2441, 2644, 2847, 3050, 3342, 3346, 3353, 3545, 3549, 3556, 3558, 3712, 3714, 3748, 3752, 3759, 3761, 3917, 3924, 3951, 3955, 3962, 3964, 4118, 4120, 4127, 4158, 4165, 4167, 4273, 4275, 4290, 4320, 4380, 4585, 4605, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[1,0,0],[2,0,0]]», Finite.of_fintype _, by decideFin!⟩
