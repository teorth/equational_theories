
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[2,1,2],[0,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[2,1,2],[0,0,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[2,1,2],[0,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[2,1,2],[0,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1481, 1489, 2337, 2533, 2787] [264, 283, 1025, 1516, 1847, 2243, 2253, 2263, 2300, 2446, 2449, 2466, 2496, 2543, 2649, 2709, 2804, 3058, 3197, 3316, 3343, 3346, 3353, 3519, 3546, 3556, 3749, 3752, 3759, 3867, 3952, 3962, 4128, 4165, 4269, 4291, 4320, 4406, 4435, 4445, 4480, 4606] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[2,1,2],[0,0,2]]», Finite.of_fintype _, by decideFin!⟩
