
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,3,3,1,3],[4,2,4,0,2,4],[1,4,1,1,1,4],[5,0,5,0,5,5],[1,2,1,5,5,1],[3,4,4,4,4,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,3,3,1,3],[4,2,4,0,2,4],[1,4,1,1,1,4],[5,0,5,0,5,5],[1,2,1,5,5,1],[3,4,4,4,4,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,3,3,3,1,3],[4,2,4,0,2,4],[1,4,1,1,1,4],[5,0,5,0,5,5],[1,2,1,5,5,1],[3,4,4,4,4,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,3,3,1,3],[4,2,4,0,2,4],[1,4,1,1,1,4],[5,0,5,0,5,5],[1,2,1,5,5,1],[3,4,4,4,4,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1868] [3457, 3518, 3521, 4067] :=
    ⟨Fin 6, «FinitePoly [[1,3,3,3,1,3],[4,2,4,0,2,4],[1,4,1,1,1,4],[5,0,5,0,5,5],[1,2,1,5,5,1],[3,4,4,4,4,3]]», by decideFin!⟩
