
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,3,2,3],[0,3,3,3],[2,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,3,2,3],[0,3,3,3],[2,0,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,3,2,3],[0,3,3,3],[2,0,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,3,2,3],[0,3,3,3],[2,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [319, 2990, 3007] [47, 99, 151, 203, 263, 273, 283, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2849, 2852, 2855, 2865, 2875, 2902, 2912, 2936, 2939, 2949, 3050, 3261, 3269, 3281, 3306, 3309, 3316, 3319, 3343, 3346, 3353, 3471, 3474, 3481, 3484, 3509, 3512, 3519, 3522, 3546, 3549, 3661, 3667, 3687, 3712, 3722, 3749, 3759, 3862, 4065, 4284, 4291, 4362, 4380, 4587, 4599, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,3,2,3],[0,3,3,3],[2,0,1,3]]», by decideFin!⟩
