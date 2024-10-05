
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4],[2,0,3,4,1],[1,4,0,2,3],[4,3,1,0,2],[3,2,4,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4],[2,0,3,4,1],[1,4,0,2,3],[4,3,1,0,2],[3,2,4,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,3,4],[2,0,3,4,1],[1,4,0,2,3],[4,3,1,0,2],[3,2,4,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4],[2,0,3,4,1],[1,4,0,2,3],[4,3,1,0,2],[3,2,4,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2714] [411, 614, 817, 1036, 1045, 1049, 1075, 1223, 1426, 1635, 1682, 1691, 1840, 1848, 1921, 1925, 2035, 2238, 2447, 2459, 2503, 2541, 2650, 2660, 2669, 2699, 2744, 2847, 3056, 3068, 3112, 3116, 3150, 3253, 3462, 3474, 3511, 3545, 3549, 3558, 3667, 3675, 3714, 3721, 3725, 3761, 3862, 4071, 4083, 4120, 4158, 4167, 4275, 4283, 4290, 4380, 4588, 4598, 4635] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,3,4],[2,0,3,4,1],[1,4,0,2,3],[4,3,1,0,2],[3,2,4,1,0]]», by decideFin!⟩
