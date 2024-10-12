
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,4,4,4],[0,3,3,3,3],[0,0,0,0,0],[3,3,3,3,3],[0,0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,4,4,4,4],[0,3,3,3,3],[0,0,0,0,0],[3,3,3,3,3],[0,0,0,0,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,4,4,4,4],[0,3,3,3,3],[0,0,0,0,0],[3,3,3,3,3],[0,0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,4,4,4,4],[0,3,3,3,3],[0,0,0,0,0],[3,3,3,3,3],[0,0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3527] [4314] :=
    ⟨Fin 5, «FinitePoly [[2,4,4,4,4],[0,3,3,3,3],[0,0,0,0,0],[3,3,3,3,3],[0,0,0,0,0]]», by decideFin!⟩
