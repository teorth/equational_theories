
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [104, 107, 1254, 1262, 3902, 4293] [8, 100, 105, 108, 359, 411, 817, 1020, 1025, 1028, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1224, 1226, 1229, 1231, 1239, 1242, 1249, 1252, 1832, 1857, 1860, 1861, 3255, 3306, 3315, 3318, 3319, 3660, 3661, 3685, 3687, 3721, 3724, 3725, 3864, 3865, 3887, 3888, 3910, 3915, 3928, 4065, 4092, 4096, 4098, 4101, 4104, 4131, 4269, 4314, 4583, 4591, 4598, 4606, 4608, 4626, 4631, 4636, 4647, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]», by decideFin!⟩
