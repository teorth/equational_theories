
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,0,4],[0,1,3,4,2],[2,1,3,0,4],[2,1,3,0,4],[2,1,3,0,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,0,4],[0,1,3,4,2],[2,1,3,0,4],[2,1,3,0,4],[2,1,3,0,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,1,3,0,4],[0,1,3,4,2],[2,1,3,0,4],[2,1,3,0,4],[2,1,3,0,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,0,4],[0,1,3,4,2],[2,1,3,0,4],[2,1,3,0,4],[2,1,3,0,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1594] [4320] :=
    ⟨Fin 5, «FinitePoly [[2,1,3,0,4],[0,1,3,4,2],[2,1,3,0,4],[2,1,3,0,4],[2,1,3,0,4]]», by decideFin!⟩
