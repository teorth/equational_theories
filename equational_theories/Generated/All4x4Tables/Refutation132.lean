
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1032, 1453, 1655, 2260, 2467, 2650, 3317, 3320, 3714, 4433] [50, 378, 416, 417, 419, 420, 429, 619, 620, 622, 623, 819, 820, 823, 1021, 1039, 1224, 1232, 1428, 1429, 1630, 1638, 1833, 1837, 1840, 1858, 2036, 2243, 2246, 2443, 2646, 2660, 2662, 2673, 2852, 2853, 2855, 2863, 2872, 3056, 3068, 3069, 3076, 3085, 3255, 3256, 3259, 3261, 3262, 3306, 3308, 3457, 3458, 3462, 3464, 3465, 3509, 3511, 3512, 3660, 3712, 3721, 3725, 3864, 3918, 3928, 4066, 4071, 4120, 4121, 4268, 4270, 4283, 4398, 4435, 4473, 4583, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]», Finite.of_fintype _, by decideFin!⟩
