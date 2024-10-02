
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 3, 3], [3, 0, 2, 3], [1, 0, 0, 1], [0, 1, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 3, 3], [3, 0, 2, 3], [1, 0, 0, 1], [0, 1, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 3, 3], [3, 0, 2, 3], [1, 0, 0, 1], [0, 1, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 3, 3], [3, 0, 2, 3], [1, 0, 0, 1], [0, 1, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [40, 211, 2472, 2484, 4658] [2, 3, 8, 23, 38, 39, 43, 47, 99, 151, 204, 205, 206, 208, 209, 212, 218, 219, 221, 222, 228, 229, 231, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2442, 2444, 2446, 2447, 2450, 2457, 2459, 2460, 2467, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3664, 3667, 3668, 3674, 3675, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 3, 3], [3, 0, 2, 3], [1, 0, 0, 1], [0, 1, 3, 0]]», by decideFin!⟩
