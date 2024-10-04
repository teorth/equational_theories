
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [56, 1035, 1050] [3, 8, 23, 38, 49, 50, 52, 53, 55, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1022, 1023, 1025, 1026, 1028, 1029, 1036, 1038, 1039, 1045, 1046, 1223, 1426, 1629, 1832, 2035, 2048, 2050, 2051, 2053, 2054, 2060, 2061, 2063, 2064, 2238, 2441, 2459, 2460, 2466, 2467, 2469, 2470, 2644, 2687, 2689, 2692, 2847, 2865, 2866, 2872, 2873, 2875, 2876, 3050, 3094, 3095, 3096, 3097, 3099, 3100, 3253, 3264, 3265, 3266, 3306, 3309, 3315, 3318, 3456, 3509, 3511, 3512, 3659, 3712, 3716, 3862, 3915, 3918, 3919, 3921, 4065, 4118, 4120, 4121, 4124, 4127, 4128, 4130, 4131, 4268, 4269, 4270, 4283, 4284, 4314, 4317, 4318, 4380, 4507, 4510, 4511, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]», by decideFin!⟩
