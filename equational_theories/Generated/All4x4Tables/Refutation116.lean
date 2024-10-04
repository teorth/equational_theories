
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1442, 1523, 2051, 2090, 2132, 3497, 3511, 3549, 3903, 3917, 3955] [8, 43, 411, 614, 817, 1020, 1223, 1432, 1434, 1455, 1479, 1492, 1526, 1528, 1558, 1629, 1832, 2041, 2043, 2053, 2060, 2064, 2088, 2097, 2101, 2135, 2137, 2167, 2238, 2441, 2644, 2847, 3050, 3253, 3459, 3481, 3509, 3518, 3522, 3545, 3556, 3558, 3588, 3667, 3675, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3865, 3887, 3915, 3928, 3951, 3962, 3964, 3994, 4065, 4098, 4118, 4120, 4127, 4131, 4154, 4158, 4165, 4167, 4273, 4275, 4283, 4290, 4320, 4380, 4585, 4588, 4598, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,1],[3,3,0,2],[1,3,3,0],[2,0,1,3]]», by decideFin!⟩
