
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 1 * x + 2 * y + 4 * x * y) % 5' (0, 202, 204, 2237, 2239, 2242, 2245, 2248, 2440, 2458)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + x + 2 * y + 4 * x * y

/-! The facts -/
theorem «Facts from FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 205, 2238, 2459] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 204, 206, 208, 209, 211, 212, 218, 219, 221, 222, 228, 229, 231, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2239, 2241, 2244, 2247, 2253, 2254, 2256, 2257, 2263, 2264, 2266, 2267, 2290, 2291, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2340, 2442, 2443, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2460, 2466, 2467, 2469, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 5, «FinitePoly 2 * x² + 2 * y² + x + 2 * y + 4 * x * y % 5», by decideFin!⟩
