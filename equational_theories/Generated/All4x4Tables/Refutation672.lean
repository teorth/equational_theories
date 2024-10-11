
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,1,3,1],[2,2,4,2,4],[1,3,1,3,1],[1,3,1,3,1],[2,2,4,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,1,3,1],[2,2,4,2,4],[1,3,1,3,1],[1,3,1,3,1],[2,2,4,2,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,3,1,3,1],[2,2,4,2,4],[1,3,1,3,1],[1,3,1,3,1],[2,2,4,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,1,3,1],[2,2,4,2,4],[1,3,1,3,1],[1,3,1,3,1],[2,2,4,2,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4001] [4587, 4606] :=
    ⟨Fin 5, «FinitePoly [[1,3,1,3,1],[2,2,4,2,4],[1,3,1,3,1],[1,3,1,3,1],[2,2,4,2,4]]», by decideFin!⟩
