
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[2,3,0,2],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,1],[2,3,0,2],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,3,1],[2,3,0,2],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,1],[2,3,0,2],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [31, 2558, 2588] [211, 221, 2238, 2446, 2533, 2659, 2672, 2696, 2699, 2709, 3068, 3105, 3253, 3458, 3459, 3461, 3481, 3511, 3518, 3519, 3664, 3674, 3677, 3714, 3721, 3725, 3749, 3862, 4068, 4120, 4127, 4131, 4269, 4270, 4272, 4283, 4320, 4380, 4598] :=
    ⟨Fin 4, «FinitePoly [[2,0,3,1],[2,3,0,2],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
