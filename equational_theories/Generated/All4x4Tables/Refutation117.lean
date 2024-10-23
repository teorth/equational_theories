
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,0,2],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,0,2],[0,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,0,2],[0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,0,2],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [316, 2909, 3007, 3297] [47, 99, 151, 203, 283, 323, 411, 614, 817, 1020, 1223, 1426, 1631, 1634, 1644, 1654, 1657, 1681, 1684, 1691, 1694, 1721, 1728, 1832, 2035, 2238, 2443, 2449, 2459, 2469, 2493, 2496, 2506, 2530, 2533, 2540, 2543, 2644, 2849, 2852, 2853, 2855, 2862, 2863, 2865, 2875, 2902, 2912, 2939, 2949, 3050, 3255, 3259, 3271, 3281, 3308, 3309, 3315, 3316, 3319, 3343, 3346, 3353, 3456, 3661, 3667, 3687, 3712, 3722, 3725, 3749, 3752, 3759, 3862, 4065, 4269, 4273, 4275, 4283, 4284, 4291, 4314, 4320, 4321, 4380, 4584, 4585, 4587, 4598, 4599, 4606, 4635, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,0,2],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
