
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 3 * x + 1 * y + 0 * x * y) % 5' (0, 98, 104, 126, 150, 166, 178, 2237, 2243, 2253, 2290, 2339, 3049, 3055, 3067, 3078, 3090, 3105, 3111, 3151, 3200, 4292, 4319, 4361, 4587, 4646, 4657)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 3 * x + y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 3 * x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 3 * x + y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [105, 127, 167, 179, 2244, 2254, 2291, 2340, 3106, 3201, 4293, 4588, 4658] [2, 3, 8, 23, 38, 39, 40, 43, 47, 100, 101, 102, 104, 107, 108, 114, 115, 117, 118, 124, 125, 152, 153, 154, 156, 157, 159, 160, 166, 169, 170, 176, 177, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2239, 2240, 2241, 2243, 2246, 2247, 2253, 2256, 2257, 2263, 2264, 2266, 2267, 2290, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2441, 2644, 2847, 3051, 3052, 3053, 3055, 3058, 3059, 3065, 3066, 3069, 3075, 3076, 3078, 3102, 3103, 3105, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4314, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636] :=
    ⟨Fin 5, «FinitePoly 3 * x + y % 5», by decideFin!⟩
