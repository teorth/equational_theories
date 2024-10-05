
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [978] [466, 1848] :=
    ⟨Fin 8, «FinitePoly [[5,3,1,2,7,0,6,4],[2,5,4,3,0,1,7,6],[4,7,5,1,6,2,0,3],[6,4,0,5,1,3,2,7],[0,2,7,6,5,4,3,1],[7,6,2,4,3,5,1,0],[1,0,3,7,4,6,5,2],[3,1,6,0,2,7,4,5]]», by decideFin!⟩
