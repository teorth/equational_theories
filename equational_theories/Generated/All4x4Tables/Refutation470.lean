
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[2,3,1,0],[1,2,3,2],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[2,3,1,0],[1,2,3,2],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[2,3,1,0],[1,2,3,2],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[2,3,1,0],[1,2,3,2],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3147] [411, 614, 817, 1020, 1223, 1426, 1635, 1682, 1684, 1691, 1840, 1848, 1894, 1921, 1925, 2035, 2238, 2443, 2446, 2447, 2456, 2459, 2469, 2503, 2506, 2534, 2541, 2650, 2660, 2669, 2697, 2699, 2710, 2744, 2847, 3056, 3068, 3112, 3116, 3150, 3253, 3462, 3474, 3511, 3545, 3549, 3556, 3558, 3667, 3675, 3714, 3721, 3725, 3748, 3752, 3761, 3862, 4071, 4083, 4120, 4158, 4167, 4273, 4275, 4283, 4290, 4320, 4380, 4588, 4598, 4635, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[2,3,1,0],[1,2,3,2],[0,1,2,3]]», by decideFin!⟩
