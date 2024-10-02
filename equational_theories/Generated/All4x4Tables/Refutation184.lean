
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 1, 3], [3, 2, 2, 1], [1, 1, 2, 3], [0, 1, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 1, 3], [3, 2, 2, 1], [1, 1, 2, 3], [0, 1, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 1, 3], [3, 2, 2, 1], [1, 1, 2, 3], [0, 1, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 1, 3], [3, 2, 2, 1], [1, 1, 2, 3], [0, 1, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [203, 307, 2238, 2644, 3105, 3659] [3, 8, 29, 31, 47, 99, 151, 204, 205, 206, 208, 209, 211, 212, 218, 219, 221, 222, 228, 229, 231, 255, 308, 309, 310, 312, 313, 315, 323, 325, 326, 333, 335, 359, 411, 614, 817, 1020, 1223, 1426, 1630, 1632, 1637, 1718, 1731, 1832, 2035, 2240, 2243, 2246, 2443, 2466, 2530, 2646, 2652, 2662, 2706, 2733, 2746, 2847, 3254, 3255, 3256, 3261, 3269, 3278, 3306, 3315, 3318, 3319, 3353, 3457, 3464, 3472, 3509, 3660, 3684, 3722, 3862, 4068, 4090, 4127, 4131, 4165, 4268, 4380] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 1, 3], [3, 2, 2, 1], [1, 1, 2, 3], [0, 1, 0, 3]]», by decideFin!⟩
