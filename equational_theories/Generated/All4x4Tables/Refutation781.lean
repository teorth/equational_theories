
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,4,2,3,4],[2,1,2,2,3],[3,4,2,0,0],[0,4,0,3,4],[3,1,1,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,4,2,3,4],[2,1,2,2,3],[3,4,2,0,0],[0,4,0,3,4],[3,1,1,3,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,4,2,3,4],[2,1,2,2,3],[3,4,2,0,0],[0,4,0,3,4],[3,1,1,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,4,2,3,4],[2,1,2,2,3],[3,4,2,0,0],[0,4,0,3,4],[3,1,1,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3122] [280, 619, 832, 1025, 1035, 1045, 1248, 1478, 1634, 1681, 1847, 1884, 1921, 2124, 2243, 2253, 2263, 2290, 2300, 2327, 2337, 2446, 2466, 2493, 2503, 2530, 2540, 2649, 2669, 2706, 2733, 2743, 2919, 2946, 2973, 3075, 3149, 3306, 3309, 3316, 3343, 3346, 3353, 3461, 3509, 3519, 3546, 3556, 3674, 3712, 3749, 3752, 3759, 3867, 3877, 3887, 3925, 3952, 3962, 4090, 4128, 4165, 4192, 4284, 4291, 4320, 4396, 4406, 4435, 4445, 4480, 4606, 4666] :=
    ⟨Fin 5, «FinitePoly [[0,4,2,3,4],[2,1,2,2,3],[3,4,2,0,0],[0,4,0,3,4],[3,1,1,3,4]]», Finite.of_fintype _, by decideFin!⟩
