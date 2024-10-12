
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,4,4,0],[2,1,4,4,1],[0,3,4,4,0],[0,1,4,4,1],[2,3,4,4,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,4,4,0],[2,1,4,4,1],[0,3,4,4,0],[0,1,4,4,1],[2,3,4,4,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,4,4,0],[2,1,4,4,1],[0,3,4,4,0],[0,1,4,4,1],[2,3,4,4,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,4,4,0],[2,1,4,4,1],[0,3,4,4,0],[0,1,4,4,1],[2,3,4,4,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1484] [4606] :=
    ⟨Fin 5, «FinitePoly [[0,1,4,4,0],[2,1,4,4,1],[0,3,4,4,0],[0,1,4,4,1],[2,3,4,4,0]]», by decideFin!⟩
