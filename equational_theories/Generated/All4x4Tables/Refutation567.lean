
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,4,1,4],[2,4,4,1,4],[2,3,2,1,2],[2,3,2,1,2],[1,0,0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,4,4,1,4],[2,4,4,1,4],[2,3,2,1,2],[2,3,2,1,2],[1,0,0,1,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,4,4,1,4],[2,4,4,1,4],[2,3,2,1,2],[2,3,2,1,2],[1,0,0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,4,4,1,4],[2,4,4,1,4],[2,3,2,1,2],[2,3,2,1,2],[1,0,0,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1863] [4065] :=
    ⟨Fin 5, «FinitePoly [[1,4,4,1,4],[2,4,4,1,4],[2,3,2,1,2],[2,3,2,1,2],[1,0,0,1,1]]», by decideFin!⟩
