
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [52, 55, 635, 645, 856, 1441, 1451, 3925, 3928] [53, 56, 105, 107, 108, 154, 157, 159, 160, 206, 209, 211, 212, 258, 261, 263, 264, 411, 617, 619, 622, 623, 630, 633, 640, 643, 818, 819, 820, 823, 825, 826, 833, 836, 843, 846, 1020, 1223, 1427, 1428, 1429, 1431, 1432, 1434, 1435, 1442, 1444, 1445, 1452, 1455, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3865, 3868, 3871, 3915, 3917, 3918, 3927, 4066, 4068, 4071, 4074, 4118, 4120, 4121, 4127, 4128, 4130, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4585, 4598, 4599, 4606, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]]», by decideFin!⟩
