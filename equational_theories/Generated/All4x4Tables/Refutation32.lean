
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,1],[2,2,1,2],[2,2,2,2],[0,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,1],[2,2,1,2],[2,2,2,2],[0,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,1],[2,2,1,2],[2,2,2,2],[0,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,1],[2,2,1,2],[2,2,2,2],[0,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [11, 109, 1257, 1262, 1263, 1264, 1267, 4097, 4105] [104, 105, 413, 426, 427, 429, 430, 437, 439, 832, 833, 836, 1022, 1023, 1025, 1035, 1038, 1039, 1045, 1046, 1048, 1230, 1234, 1240, 1243, 1244, 1245, 1246, 1258, 1259, 1260, 1266, 1834, 1847, 1850, 1851, 1860, 3255, 3316, 3318, 3724, 3864, 3865, 3867, 3881, 3888, 3925, 4072, 4076, 4131, 4269, 4314, 4598, 4606, 4611, 4620, 4631, 4636, 4647, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,1],[2,2,1,2],[2,2,2,2],[0,0,3,2]]», by decideFin!⟩
