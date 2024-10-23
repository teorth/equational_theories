
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,2,0],[2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,2,0],[2,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,2,0],[2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,2,0],[2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1897] [99, 151, 359, 411, 1020, 1223, 1631, 1634, 1637, 1644, 1654, 1657, 1681, 1684, 1691, 1694, 1721, 1728, 1834, 1837, 1840, 1847, 1860, 1921, 2035, 3253, 3867, 3877, 3887, 3915, 3925, 3952, 3962, 4275, 4320, 4587, 4606] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,2,0],[2,1,0]]», Finite.of_fintype _, by decideFin!⟩
