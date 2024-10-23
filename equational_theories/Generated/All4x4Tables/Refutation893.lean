
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,3,7,2,4,6,0],[2,0,7,3,1,6,4,5],[4,3,5,0,6,1,2,7],[5,1,4,6,0,3,7,2],[3,4,1,2,7,5,0,6],[6,7,0,5,4,2,1,3],[0,2,6,4,5,7,3,1],[7,6,2,1,3,0,5,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,3,7,2,4,6,0],[2,0,7,3,1,6,4,5],[4,3,5,0,6,1,2,7],[5,1,4,6,0,3,7,2],[3,4,1,2,7,5,0,6],[6,7,0,5,4,2,1,3],[0,2,6,4,5,7,3,1],[7,6,2,1,3,0,5,4]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,5,3,7,2,4,6,0],[2,0,7,3,1,6,4,5],[4,3,5,0,6,1,2,7],[5,1,4,6,0,3,7,2],[3,4,1,2,7,5,0,6],[6,7,0,5,4,2,1,3],[0,2,6,4,5,7,3,1],[7,6,2,1,3,0,5,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,3,7,2,4,6,0],[2,0,7,3,1,6,4,5],[4,3,5,0,6,1,2,7],[5,1,4,6,0,3,7,2],[3,4,1,2,7,5,0,6],[6,7,0,5,4,2,1,3],[0,2,6,4,5,7,3,1],[7,6,2,1,3,0,5,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2866] [255, 2035, 2644, 2852, 3253, 3456, 4268, 4314, 4598] :=
    ⟨Fin 8, «FinitePoly [[1,5,3,7,2,4,6,0],[2,0,7,3,1,6,4,5],[4,3,5,0,6,1,2,7],[5,1,4,6,0,3,7,2],[3,4,1,2,7,5,0,6],[6,7,0,5,4,2,1,3],[0,2,6,4,5,7,3,1],[7,6,2,1,3,0,5,4]]», Finite.of_fintype _, by decideFin!⟩
