
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,3,4,6,0,7,2,1],[2,5,6,7,3,4,1,0],[6,0,5,1,7,2,4,3],[3,2,0,5,1,6,7,4],[7,6,3,4,5,1,0,2],[0,1,2,3,4,5,6,7],[1,4,7,0,2,3,5,6],[4,7,1,2,6,0,3,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,3,4,6,0,7,2,1],[2,5,6,7,3,4,1,0],[6,0,5,1,7,2,4,3],[3,2,0,5,1,6,7,4],[7,6,3,4,5,1,0,2],[0,1,2,3,4,5,6,7],[1,4,7,0,2,3,5,6],[4,7,1,2,6,0,3,5]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[5,3,4,6,0,7,2,1],[2,5,6,7,3,4,1,0],[6,0,5,1,7,2,4,3],[3,2,0,5,1,6,7,4],[7,6,3,4,5,1,0,2],[0,1,2,3,4,5,6,7],[1,4,7,0,2,3,5,6],[4,7,1,2,6,0,3,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,3,4,6,0,7,2,1],[2,5,6,7,3,4,1,0],[6,0,5,1,7,2,4,3],[3,2,0,5,1,6,7,4],[7,6,3,4,5,1,0,2],[0,1,2,3,4,5,6,7],[1,4,7,0,2,3,5,6],[4,7,1,2,6,0,3,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1101] [1684, 3066] :=
    ⟨Fin 8, «FinitePoly [[5,3,4,6,0,7,2,1],[2,5,6,7,3,4,1,0],[6,0,5,1,7,2,4,3],[3,2,0,5,1,6,7,4],[7,6,3,4,5,1,0,2],[0,1,2,3,4,5,6,7],[1,4,7,0,2,3,5,6],[4,7,1,2,6,0,3,5]]», Finite.of_fintype _, by decideFin!⟩
