
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0],[1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0],[1,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[1,0],[1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0],[1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [13] [47, 105, 108, 203, 255, 307, 417, 420, 427, 430, 437, 440, 614, 817, 1023, 1026, 1029, 1036, 1039, 1046, 1049, 1086, 1113, 1224, 1226, 1229, 1239, 1242, 1249, 1252, 1426, 1632, 1635, 1638, 1648, 1655, 1722, 1833, 1838, 1841, 1848, 1851, 1858, 1861, 2036, 2038, 2041, 2044, 2238, 2441, 2644, 2847, 3050, 3256, 3259, 3262, 3308, 3315, 3318, 3456, 3659, 3865, 3868, 3871, 3878, 3917, 3924, 3927, 4066, 4068, 4071, 4074, 4120, 4127, 4130, 4268, 4270, 4273, 4283, 4314, 4380, 4583, 4585, 4591, 4598, 4605, 4629] :=
    ⟨Fin 2, «FinitePoly [[1,0],[1,0]]», Finite.of_fintype _, by decideFin!⟩
