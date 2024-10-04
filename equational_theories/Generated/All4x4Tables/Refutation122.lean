
import equational_theories.AllEquations
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
  ∃ (G : Type) (_ : Magma G), Facts G [48, 102, 618, 827, 1026] [50, 160, 212, 258, 261, 263, 362, 416, 417, 419, 420, 436, 619, 620, 622, 623, 630, 819, 820, 822, 823, 1021, 1022, 1023, 1025, 1036, 1038, 1045, 1224, 1228, 1231, 1232, 1239, 1241, 1248, 1428, 1429, 1435, 1442, 1444, 1445, 1630, 1833, 1837, 1838, 1861, 2036, 2050, 2051, 2053, 2243, 2246, 2443, 2646, 2852, 3255, 3256, 3320, 3457, 3511, 3518, 3521, 3660, 3662, 3665, 3725, 3864, 3867, 3870, 3917, 3924, 3927, 4066, 4067, 4068, 4070, 4071, 4127, 4268, 4270, 4314, 4398, 4435, 4472, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]», by decideFin!⟩
