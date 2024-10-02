
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 1, 3], [3, 0, 0, 1], [3, 0, 2, 2], [2, 3, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 1, 3], [3, 0, 0, 1], [3, 0, 2, 2], [2, 3, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 1, 3], [3, 0, 0, 1], [3, 0, 2, 2], [2, 3, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 1, 3], [3, 0, 0, 1], [3, 0, 2, 2], [2, 3, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [53, 1038, 1629, 3724, 4068] [3, 8, 23, 48, 49, 50, 52, 55, 56, 62, 63, 65, 66, 72, 73, 75, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1023, 1036, 1045, 1073, 1075, 1109, 1113, 1122, 1223, 1426, 1632, 1635, 1645, 1648, 1657, 1684, 1695, 1719, 1728, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3462, 3472, 3481, 3511, 3522, 3549, 3558, 3660, 3661, 3662, 3667, 3677, 3678, 3684, 3685, 3715, 3722, 3725, 3748, 3749, 3761, 3862, 4074, 4083, 4091, 4118, 4130, 4158, 4164, 4273, 4290, 4380, 4588, 4605] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 1, 3], [3, 0, 0, 1], [3, 0, 2, 2], [2, 3, 3, 0]]», by decideFin!⟩
