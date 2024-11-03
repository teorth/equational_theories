
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[0,1,2],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[0,1,2],[0,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[0,1,2],[0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[0,1,2],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [312, 323, 2493, 2899, 4606] [47, 99, 151, 203, 263, 280, 283, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2037, 2040, 2043, 2053, 2060, 2063, 2087, 2124, 2127, 2134, 2238, 2443, 2449, 2459, 2466, 2469, 2496, 2506, 2530, 2533, 2540, 2543, 2646, 2652, 2662, 2672, 2699, 2709, 2736, 2743, 2746, 2849, 2852, 2855, 2862, 2865, 2872, 2875, 2902, 2909, 2912, 2939, 2946, 2949, 3050, 3255, 3261, 3271, 3281, 3326, 3343, 3346, 3353, 3456, 3661, 3667, 3677, 3687, 3722, 3725, 3752, 3759, 3862, 4065, 4269, 4275, 4291, 4314, 4320, 4380, 4584, 4587, 4590, 4599, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[0,1,2],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
