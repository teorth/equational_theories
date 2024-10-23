
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,0],[2,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,0],[2,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,0],[2,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,0],[2,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2949] [1629, 2238, 2441, 2652, 2662, 2669, 2673, 2697, 2699, 2744, 2855, 2865, 2872, 2900, 2902, 2909, 3050, 3256, 3259, 3261, 3271, 3278, 3306, 3308, 3315, 3342, 3456, 3659, 3862, 4065, 4270, 4273, 4283, 4290, 4320, 4386, 4396, 4398, 4405, 4409, 4433, 4435, 4442, 4473, 4480, 4482, 4598, 4622, 4635, 4656] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,0],[2,1,1]]», Finite.of_fintype _, by decideFin!⟩
