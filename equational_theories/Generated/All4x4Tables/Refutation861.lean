
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,3,0],[0,4,1,2,3],[2,0,3,1,4],[4,3,2,0,1],[3,1,0,4,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,3,0],[0,4,1,2,3],[2,0,3,1,4],[4,3,2,0,1],[3,1,0,4,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,4,3,0],[0,4,1,2,3],[2,0,3,1,4],[4,3,2,0,1],[3,1,0,4,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,3,0],[0,4,1,2,3],[2,0,3,1,4],[4,3,2,0,1],[3,1,0,4,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [546, 826, 3113] [47, 255, 417, 440, 614, 825, 846, 1020, 1637, 1645, 1684, 1692, 1722, 1731, 1857, 1894, 1922, 2444, 2466, 2496, 2504, 2530, 2534, 2543, 2644, 2847, 3056, 3068, 3253, 3472, 3556, 3659, 4071, 4120, 4273, 4293, 4598] :=
    ⟨Fin 5, «FinitePoly [[1,2,4,3,0],[0,4,1,2,3],[2,0,3,1,4],[4,3,2,0,1],[3,1,0,4,2]]», Finite.of_fintype _, by decideFin!⟩
