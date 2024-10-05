
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,1],[3,4,2,1,0],[4,0,1,3,2],[1,3,0,2,4],[2,1,4,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,1],[3,4,2,1,0],[4,0,1,3,2],[1,3,0,2,4],[2,1,4,0,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,3,4,1],[3,4,2,1,0],[4,0,1,3,2],[1,3,0,2,4],[2,1,4,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,1],[3,4,2,1,0],[4,0,1,3,2],[1,3,0,2,4],[2,1,4,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2497, 2586, 3142] [47, 203, 417, 419, 436, 440, 466, 477, 511, 614, 825, 835, 842, 846, 870, 883, 906, 1020, 1223, 1426, 1635, 1637, 1645, 1684, 1691, 1722, 1731, 1840, 1848, 1857, 1894, 1921, 2035, 2238, 2444, 2447, 2459, 2466, 2496, 2530, 2534, 2540, 2543, 2644, 2847, 3056, 3068, 3105, 3112, 3116, 3143, 3150, 3152, 3253, 3462, 3464, 3472, 3481, 3509, 3511, 3545, 3549, 3556, 3659, 3862, 4071, 4083, 4090, 4120, 4158, 4165, 4167, 4270, 4273, 4275, 4283, 4320, 4380, 4588, 4590, 4598, 4605, 4635] :=
    ⟨Fin 5, «FinitePoly [[0,2,3,4,1],[3,4,2,1,0],[4,0,1,3,2],[1,3,0,2,4],[2,1,4,0,3]]», by decideFin!⟩
