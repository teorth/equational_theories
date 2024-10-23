
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,1,0,2],[0,2,3,1],[1,3,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,1,0,2],[0,2,3,1],[1,3,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,1,0,2],[0,2,3,1],[1,3,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,1,0,2],[0,2,3,1],[1,3,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [63, 1692, 1694, 1719, 1721, 1888, 1931, 2497, 2504, 2533, 2540, 3482, 3484, 3546, 3548] [65, 73, 99, 151, 203, 255, 359, 411, 614, 817, 1020, 1223, 1426, 1635, 1637, 1645, 1657, 1684, 1691, 1722, 1731, 1840, 1848, 1857, 1894, 1921, 2035, 2238, 2444, 2447, 2459, 2466, 2496, 2506, 2530, 2534, 2543, 2644, 2847, 3076, 3105, 3112, 3113, 3115, 3116, 3142, 3143, 3150, 3152, 3253, 3458, 3461, 3462, 3464, 3472, 3475, 3481, 3509, 3511, 3545, 3549, 3555, 3556, 3659, 3862, 4083, 4084, 4090, 4091, 4093, 4121, 4157, 4158, 4165, 4167, 4270, 4273, 4275, 4283, 4284, 4320, 4380, 4588, 4590, 4599, 4605, 4606, 4608, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,1,0,2],[0,2,3,1],[1,3,2,0]]», Finite.of_fintype _, by decideFin!⟩
