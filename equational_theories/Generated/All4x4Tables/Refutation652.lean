
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3342, 3964] [307, 359, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3343, 3345, 3346, 3352, 3353, 3509, 3511, 3512, 3518, 3519, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 6, «FinitePoly [[5,1,2,0,5,4],[2,0,0,3,1,5],[1,0,0,5,2,3],[4,5,3,1,0,1],[5,2,1,4,5,0],[0,3,5,1,4,1]]», by decideFin!⟩
