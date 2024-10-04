
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [49, 621] [3, 8, 23, 38, 50, 52, 53, 55, 56, 99, 151, 203, 255, 307, 359, 411, 617, 623, 629, 630, 632, 633, 639, 640, 642, 643, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2048, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2238, 2441, 2459, 2460, 2466, 2467, 2469, 2470, 2644, 2687, 2688, 2689, 2847, 2865, 2866, 2872, 2873, 2875, 2876, 3050, 3094, 3095, 3096, 3097, 3099, 3100, 3253, 3263, 3264, 3265, 3266, 3267, 3306, 3309, 3315, 3318, 3456, 3509, 3511, 3512, 3660, 3661, 3722, 3862, 3915, 3918, 4065, 4118, 4121, 4124, 4128, 4131, 4268, 4269, 4284, 4380, 4584, 4599] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,1],[3,1,1,1],[3,2,2,2],[3,3,3,3]]», by decideFin!⟩
