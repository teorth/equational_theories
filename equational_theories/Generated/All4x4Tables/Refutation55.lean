
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,1,2],[1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,1,2],[1,1,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,1,2],[1,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,1,2],[1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 616, 619, 822, 832, 1035, 1234, 1244, 2259, 2273, 3525, 3533, 3925] [55, 107, 211, 413, 615, 620, 622, 629, 632, 639, 642, 819, 825, 835, 842, 845, 1038, 1045, 1048, 1251, 1428, 1431, 1434, 1441, 1444, 1451, 1454, 2266, 2449, 2459, 2469, 3255, 3279, 3306, 3308, 3309, 3315, 3316, 3318, 3509, 3511, 3518, 3521, 3685, 3712, 3714, 3721, 3724, 3725, 3870, 3881, 3887, 3888, 3917, 3924, 3927, 3928, 4067, 4070, 4073, 4083, 4084, 4090, 4091, 4093, 4120, 4121, 4127, 4128, 4130, 4131, 4269, 4283, 4284, 4293, 4314, 4396, 4398, 4399, 4433, 4435, 4436, 4472, 4473, 4591, 4598, 4599, 4606, 4608, 4622, 4629, 4631, 4636] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,1,2],[1,1,2]]», Finite.of_fintype _, by decideFin!⟩
