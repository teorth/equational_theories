
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,4,4,4,4,0,0,0],[2,1,5,7,1,5,1,7],[3,6,2,7,2,2,6,7],[6,6,5,3,3,5,6,3],[0,4,4,4,4,4,4,4],[5,6,5,3,5,5,6,3],[6,6,2,7,6,5,6,7],[7,6,2,7,7,2,6,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,4,4,4,4,0,0,0],[2,1,5,7,1,5,1,7],[3,6,2,7,2,2,6,7],[6,6,5,3,3,5,6,3],[0,4,4,4,4,4,4,4],[5,6,5,3,5,5,6,3],[6,6,2,7,6,5,6,7],[7,6,2,7,7,2,6,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[0,4,4,4,4,0,0,0],[2,1,5,7,1,5,1,7],[3,6,2,7,2,2,6,7],[6,6,5,3,3,5,6,3],[0,4,4,4,4,4,4,4],[5,6,5,3,5,5,6,3],[6,6,2,7,6,5,6,7],[7,6,2,7,7,2,6,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,4,4,4,4,0,0,0],[2,1,5,7,1,5,1,7],[3,6,2,7,2,2,6,7],[6,6,5,3,3,5,6,3],[0,4,4,4,4,4,4,4],[5,6,5,3,5,5,6,3],[6,6,2,7,6,5,6,7],[7,6,2,7,7,2,6,7]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [645] [832] :=
    ⟨Fin 8, «FinitePoly [[0,4,4,4,4,0,0,0],[2,1,5,7,1,5,1,7],[3,6,2,7,2,2,6,7],[6,6,5,3,3,5,6,3],[0,4,4,4,4,4,4,4],[5,6,5,3,5,5,6,3],[6,6,2,7,6,5,6,7],[7,6,2,7,7,2,6,7]]», by decideFin!⟩
