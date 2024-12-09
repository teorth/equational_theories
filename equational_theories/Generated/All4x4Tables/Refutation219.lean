
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[0,1,2],[0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,1],[0,1,2],[0,0,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[0,1,2],[0,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,1],[0,1,2],[0,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2919] [47, 99, 151, 203, 263, 280, 283, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2037, 2040, 2043, 2053, 2060, 2063, 2087, 2124, 2127, 2134, 2238, 2441, 2646, 2652, 2662, 2672, 2699, 2709, 2736, 2743, 2746, 2849, 2855, 2865, 2875, 2902, 2912, 2939, 2946, 2949, 3050, 3255, 3261, 3271, 3281, 3326, 3343, 3346, 3353, 3458, 3471, 3474, 3481, 3484, 3537, 3546, 3549, 3661, 3667, 3677, 3687, 3722, 3725, 3752, 3759, 3862, 4065, 4269, 4275, 4291, 4380, 4584, 4587, 4590, 4599, 4635] :=
    ⟨Fin 3, «All4x4Tables [[0,1,1],[0,1,2],[0,0,0]]», Finite.of_fintype _, by decideFin!⟩
