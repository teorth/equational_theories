
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [618, 827] [50, 378, 416, 417, 419, 420, 619, 620, 622, 623, 819, 820, 822, 823, 1021, 1022, 1023, 1025, 1028, 1224, 1225, 1228, 1229, 1231, 1232, 1428, 1429, 1630, 1631, 1833, 1837, 1838, 2036, 2243, 2246, 2443, 2446, 2646, 2852, 3255, 3256, 3258, 3259, 3261, 3262, 3315, 3316, 3320, 3457, 3458, 3518, 3519, 3521, 3660, 3714, 3721, 3724, 3725, 3864, 3924, 3925, 3927, 3928, 4120, 4121, 4127, 4128, 4130, 4270, 4282, 4284, 4314, 4433, 4435, 4436, 4472, 4473, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]», Finite.of_fintype _, by decideFin!⟩
