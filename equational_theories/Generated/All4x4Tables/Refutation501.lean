
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2259, 2277, 2281, 2296, 2314, 2318, 2368, 2372, 2469, 3050] [204, 206, 208, 209, 212, 218, 219, 222, 228, 229, 231, 1020, 2239, 2241, 2244, 2247, 2254, 2257, 2263, 2264, 2267, 2291, 2294, 2300, 2301, 2304, 2327, 2328, 2331, 2337, 2338, 2340, 2442, 2444, 2446, 2447, 2450, 2456, 2457, 2459, 2460, 2466, 2467, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 2644, 3052, 3055, 3056, 3058, 3065, 3068, 3075, 3078, 3079, 3102, 3105, 3112, 3115, 3139, 3142, 3149, 3152, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3751, 3752, 3759, 3761] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 1, 3], [3, 3, 3, 3], [3, 3, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
