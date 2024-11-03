
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,5,5,2],[4,4,4,4,4,4],[5,3,2,0,0,3],[2,0,5,3,3,0],[1,1,1,1,1,1],[3,5,0,2,2,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,5,5,2],[4,4,4,4,4,4],[5,3,2,0,0,3],[2,0,5,3,3,0],[1,1,1,1,1,1],[3,5,0,2,2,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,2,3,5,5,2],[4,4,4,4,4,4],[5,3,2,0,0,3],[2,0,5,3,3,0],[1,1,1,1,1,1],[3,5,0,2,2,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,5,5,2],[4,4,4,4,4,4],[5,3,2,0,0,3],[2,0,5,3,3,0],[1,1,1,1,1,1],[3,5,0,2,2,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [206, 1648] [159, 1432, 1451, 1635, 1657, 1841, 1848, 1860, 2247, 2256, 2264, 2457, 2459, 3259, 3308, 3319, 3462] :=
    ⟨Fin 6, «FinitePoly [[0,2,3,5,5,2],[4,4,4,4,4,4],[5,3,2,0,0,3],[2,0,5,3,3,0],[1,1,1,1,1,1],[3,5,0,2,2,5]]», Finite.of_fintype _, by decideFin!⟩
