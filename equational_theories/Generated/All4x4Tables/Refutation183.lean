import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,1],[3,2,1,2],[0,1,2,0],[2,0,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,1],[3,2,1,2],[0,1,2,0],[2,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,1],[3,2,1,2],[0,1,2,0],[2,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,1],[3,2,1,2],[0,1,2,0],[2,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [452,658] [620,632,655,4598] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,1],[3,2,1,2],[0,1,2,0],[2,0,3,2]]», by decideFin!⟩
