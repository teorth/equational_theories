
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 1 * y**2 + 0 * x + 1 * y + 2 * x * y) % 3' (0, 202, 204, 2237, 2239, 2242, 2245, 2248, 2440, 2458, 4064, 4127, 4267, 4281)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + y² + y + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x*x + y*y + y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + y² + y + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [205, 2459, 4128, 4268] [47, 99, 151, 206, 209, 211, 212, 219, 221, 222, 228, 229, 231, 255, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2239, 2241, 2244, 2247, 2253, 2254, 2256, 2257, 2263, 2264, 2266, 2267, 2290, 2291, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2340, 2442, 2443, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2460, 2466, 2467, 2469, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly x² + y² + y + 2 * x * y % 3», by decideFin!⟩
