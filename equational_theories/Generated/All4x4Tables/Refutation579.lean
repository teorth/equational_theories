
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [194] [411, 4275] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]», by decideFin!⟩
