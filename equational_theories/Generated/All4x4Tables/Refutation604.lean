
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,2,2,2],[1,1,1,1,1],[3,3,3,3,3],[0,4,0,0,0],[4,2,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,2,2,2],[1,1,1,1,1],[3,3,3,3,3],[0,4,0,0,0],[4,2,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,0,2,2,2],[1,1,1,1,1],[3,3,3,3,3],[0,4,0,0,0],[4,2,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,2,2,2],[1,1,1,1,1],[3,3,3,3,3],[0,4,0,0,0],[4,2,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2065] [4598] :=
    ⟨Fin 5, «FinitePoly [[2,0,2,2,2],[1,1,1,1,1],[3,3,3,3,3],[0,4,0,0,0],[4,2,4,4,4]]», by decideFin!⟩
