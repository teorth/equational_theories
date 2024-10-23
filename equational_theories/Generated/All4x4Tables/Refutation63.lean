
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[0,1,2],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[0,1,2],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[0,1,2],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[0,1,2],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2259, 2277, 2281, 2296, 2314, 2318, 2368, 2372, 2443, 2449, 2459, 2469, 2493, 3664, 3684, 3712, 3749, 4380] [47, 99, 151, 231, 264, 273, 280, 283, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2244, 2247, 2254, 2300, 2340, 2444, 2456, 2457, 2460, 2466, 2467, 2496, 2506, 2530, 2533, 2540, 2543, 2644, 2847, 3050, 3253, 3456, 3661, 3662, 3665, 3667, 3668, 3674, 3677, 3687, 3722, 3724, 3725, 3752, 3759, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4291, 4314, 4320, 4383, 4396, 4398, 4399, 4406, 4433, 4435, 4445, 4470, 4473, 4583, 4584, 4587, 4590, 4598, 4599, 4606, 4629] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[0,1,2],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
