
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,0,0,2],[1,0,1,1,5,0],[3,2,3,4,2,2],[3,3,4,4,1,3],[4,5,4,1,5,4],[2,0,5,5,5,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,0,0,2],[1,0,1,1,5,0],[3,2,3,4,2,2],[3,3,4,4,1,3],[4,5,4,1,5,4],[2,0,5,5,5,0]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,0,3,0,0,2],[1,0,1,1,5,0],[3,2,3,4,2,2],[3,3,4,4,1,3],[4,5,4,1,5,4],[2,0,5,5,5,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,0,0,2],[1,0,1,1,5,0],[3,2,3,4,2,2],[3,3,4,4,1,3],[4,5,4,1,5,4],[2,0,5,5,5,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [834] [40, 105, 107, 108, 359, 411, 819, 835, 836, 842, 843, 845, 846, 3862] :=
    ⟨Fin 6, «FinitePoly [[2,0,3,0,0,2],[1,0,1,1,5,0],[3,2,3,4,2,2],[3,3,4,4,1,3],[4,5,4,1,5,4],[2,0,5,5,5,0]]», Finite.of_fintype _, by decideFin!⟩
