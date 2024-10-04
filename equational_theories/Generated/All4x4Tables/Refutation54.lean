
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [13, 3356] [3, 11, 23, 38, 47, 100, 102, 105, 108, 152, 154, 157, 160, 203, 255, 307, 360, 362, 377, 412, 414, 417, 420, 427, 430, 437, 440, 614, 817, 1021, 1023, 1026, 1029, 1036, 1039, 1046, 1049, 1224, 1226, 1229, 1232, 1239, 1242, 1249, 1252, 1426, 1630, 1632, 1635, 1638, 1645, 1648, 1655, 1658, 1833, 1835, 1838, 1841, 1848, 1851, 1858, 1861, 2036, 2038, 2041, 2044, 2051, 2054, 2061, 2064, 2238, 2441, 2644, 2847, 3050, 3254, 3256, 3259, 3262, 3308, 3315, 3318, 3456, 3659, 3865, 3868, 3871, 3917, 3924, 3927, 4066, 4068, 4071, 4074, 4120, 4127, 4130, 4268, 4270, 4283, 4314, 4380, 4583, 4585, 4598, 4629] :=
    ⟨Fin 4, «FinitePoly [[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]]», by decideFin!⟩
