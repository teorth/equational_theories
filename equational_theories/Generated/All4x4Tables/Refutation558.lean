
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,5,1,5,2],[5,3,3,1,5,0],[5,3,0,1,5,0],[1,3,5,1,5,2],[5,3,5,1,5,0],[2,0,0,2,5,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,5,1,5,2],[5,3,3,1,5,0],[5,3,0,1,5,0],[1,3,5,1,5,2],[5,3,5,1,5,0],[2,0,0,2,5,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,3,5,1,5,2],[5,3,3,1,5,0],[5,3,0,1,5,0],[1,3,5,1,5,2],[5,3,5,1,5,0],[2,0,0,2,5,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,5,1,5,2],[5,3,3,1,5,0],[5,3,0,1,5,0],[1,3,5,1,5,2],[5,3,5,1,5,0],[2,0,0,2,5,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2169] [3877] :=
    ⟨Fin 6, «FinitePoly [[2,3,5,1,5,2],[5,3,3,1,5,0],[5,3,0,1,5,0],[1,3,5,1,5,2],[5,3,5,1,5,0],[2,0,0,2,5,4]]», by decideFin!⟩
