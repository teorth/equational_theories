
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1,1],[2,2,2,2,4],[0,4,4,3,4],[1,1,2,1,1],[0,1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1,1],[2,2,2,2,4],[0,4,4,3,4],[1,1,2,1,1],[0,1,3,3,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,2,1,1],[2,2,2,2,4],[0,4,4,3,4],[1,1,2,1,1],[0,1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1,1],[2,2,2,2,4],[0,4,4,3,4],[1,1,2,1,1],[0,1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2665] [3253, 3456, 4631] :=
    ⟨Fin 5, «FinitePoly [[1,2,2,1,1],[2,2,2,2,4],[0,4,4,3,4],[1,1,2,1,1],[0,1,3,3,3]]», by decideFin!⟩
