
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 0, 0, 3], [1, 3, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 0, 0, 3], [1, 3, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 0, 0, 3], [1, 3, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 0, 0, 3], [1, 3, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [205, 231, 2296, 2351, 2406, 2746, 3152, 3464, 4276] [3, 8, 23, 47, 99, 151, 204, 206, 208, 209, 211, 212, 218, 219, 221, 222, 228, 229, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2253, 2256, 2263, 2300, 2303, 2327, 2337, 2441, 2646, 2649, 2659, 2662, 2669, 2696, 2706, 2733, 2743, 2847, 3051, 3052, 3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3253, 3458, 3461, 3509, 3512, 3519, 3522, 3546, 3659, 3862, 4065, 4320, 4380, 4587] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 0, 0, 3], [1, 3, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
