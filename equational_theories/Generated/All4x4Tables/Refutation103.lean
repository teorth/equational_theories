
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [260, 2919, 3712] [47, 99, 151, 203, 263, 273, 280, 283, 307, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2849, 2855, 2865, 2875, 2902, 2912, 2936, 2939, 2946, 2949, 3050, 3255, 3258, 3261, 3268, 3271, 3278, 3281, 3309, 3316, 3319, 3343, 3346, 3353, 3456, 3661, 3664, 3667, 3674, 3677, 3687, 3722, 3759, 3862, 4065, 4275, 4320, 4380, 4587, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[3,0,3,0],[0,1,2,3],[0,2,2,3]]», by decideFin!⟩
