
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [53] [50, 56, 99, 151, 203, 255, 359, 411, 614, 817, 1021, 1023, 1028, 1029, 1035, 1036, 1039, 1045, 1046, 1048, 1049, 1223, 1426, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1648, 1654, 1655, 1657, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3457, 3458, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3712, 3714, 3721, 3722, 3725, 3862, 4066, 4067, 4070, 4071, 4074, 4118, 4120, 4121, 4127, 4128, 4130, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[3,0,0,1],[3,0,2,2],[2,3,3,0]]», Finite.of_fintype _, by decideFin!⟩
