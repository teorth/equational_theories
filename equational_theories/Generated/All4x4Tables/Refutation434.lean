
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 3, 3, 3], [1, 1, 1, 0], [1, 2, 2, 2], [0, 0, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 3, 3, 3], [1, 1, 1, 0], [1, 2, 2, 2], [0, 0, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 3, 3, 3], [1, 1, 1, 0], [1, 2, 2, 2], [0, 0, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 3, 3, 3], [1, 1, 1, 0], [1, 2, 2, 2], [0, 0, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1845, 2443, 2466, 3660, 3662, 4282, 4288] [8, 99, 204, 206, 208, 209, 212, 218, 219, 221, 222, 228, 229, 231, 307, 359, 411, 817, 1020, 1223, 2239, 2241, 2244, 2247, 2253, 2254, 2256, 2257, 2263, 2264, 2266, 2267, 2290, 2291, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2340, 2442, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2459, 2460, 2467, 2469, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 3050, 3253, 3661, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[2, 3, 3, 3], [1, 1, 1, 0], [1, 2, 2, 2], [0, 0, 0, 1]]», by decideFin!⟩
