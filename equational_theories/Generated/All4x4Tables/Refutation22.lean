
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [387] [3306, 3308, 3315, 3346, 3353, 3355, 3509, 3511, 3518, 3549, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3917, 3924, 3928, 3951, 3955, 3962, 4120, 4127, 4131, 4154, 4158, 4165, 4290, 4320, 4396, 4433, 4473, 4480, 4598, 4605] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]», by decideFin!⟩
