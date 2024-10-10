
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1,0],[1,1,1,1],[2,2,2,0],[1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1,0],[1,1,1,1],[2,2,2,0],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,1,0],[1,1,1,1],[2,2,2,0],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1,0],[1,1,1,1],[2,2,2,0],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1237] [1850, 3721, 3927, 4120, 4127, 4472, 4598] :=
    ⟨Fin 4, «FinitePoly [[0,0,1,0],[1,1,1,1],[2,2,2,0],[1,3,3,3]]», by decideFin!⟩
