
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,1,0],[1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,1,0],[1,2,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,1,0],[1,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,1,0],[1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [417, 619, 620, 622, 819, 820, 823, 825, 1023, 1026, 3259, 3315, 3462, 3464, 3662, 3928] [47, 414, 419, 427, 429, 466, 473, 477, 504, 511, 513, 617, 630, 632, 639, 643, 667, 669, 676, 680, 707, 832, 833, 835, 842, 845, 870, 872, 879, 883, 906, 917, 1028, 1038, 1045, 1075, 1082, 1086, 1109, 1113, 1122, 1223, 1426, 1629, 1838, 1840, 1848, 1857, 1861, 1885, 1887, 1894, 1921, 1925, 2035, 2238, 2441, 2644, 2847, 3050, 3261, 3269, 3271, 3278, 3279, 3306, 3308, 3342, 3346, 3353, 3459, 3472, 3474, 3481, 3509, 3511, 3518, 3522, 3545, 3549, 3558, 3685, 3864, 3867, 3870, 3878, 3880, 3881, 3887, 3888, 3917, 3924, 3925, 3955, 3962, 3964, 4065, 4269, 4270, 4273, 4275, 4283, 4293, 4314, 4320, 4380, 4584, 4585, 4588, 4590, 4591, 4598, 4606, 4608, 4635, 4636] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,1,0],[1,2,1]]», Finite.of_fintype _, by decideFin!⟩
