
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,4,1,1,4],[2,5,5,2,5,5],[0,3,0,0,3,0],[4,4,1,4,4,1],[5,2,2,5,2,2],[3,0,3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,4,1,1,4],[2,5,5,2,5,5],[0,3,0,0,3,0],[4,4,1,4,4,1],[5,2,2,5,2,2],[3,0,3,3,0,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,1,4,1,1,4],[2,5,5,2,5,5],[0,3,0,0,3,0],[4,4,1,4,4,1],[5,2,2,5,2,2],[3,0,3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,4,1,1,4],[2,5,5,2,5,5],[0,3,0,0,3,0],[4,4,1,4,4,1],[5,2,2,5,2,2],[3,0,3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2883] [2035, 3456] :=
    ⟨Fin 6, «FinitePoly [[1,1,4,1,1,4],[2,5,5,2,5,5],[0,3,0,0,3,0],[4,4,1,4,4,1],[5,2,2,5,2,2],[3,0,3,3,0,3]]», by decideFin!⟩
