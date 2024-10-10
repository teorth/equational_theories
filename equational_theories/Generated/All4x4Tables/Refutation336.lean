
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4229] [3306, 3308, 3353, 3355, 3459, 3462, 3474, 3481, 3511, 3518, 3549, 3556, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3865, 3868, 3880, 3887, 3917, 3924, 3955, 3962, 4071, 4073, 4081, 4083, 4127, 4131, 4154, 4158, 4273, 4275, 4290, 4320, 4396, 4433, 4473, 4480, 4598, 4605, 4647, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]», by decideFin!⟩
