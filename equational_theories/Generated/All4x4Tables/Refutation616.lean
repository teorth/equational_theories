
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,1,3,7,5,6,7],[2,6,3,3,2,7,6,3],[4,5,2,3,7,7,7,7],[0,1,2,3,2,7,6,2],[4,6,1,6,4,5,6,7],[0,6,3,6,4,5,6,3],[0,1,3,3,4,5,6,3],[0,5,2,5,4,4,5,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,1,3,7,5,6,7],[2,6,3,3,2,7,6,3],[4,5,2,3,7,7,7,7],[0,1,2,3,2,7,6,2],[4,6,1,6,4,5,6,7],[0,6,3,6,4,5,6,3],[0,1,3,3,4,5,6,3],[0,5,2,5,4,4,5,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,5,1,3,7,5,6,7],[2,6,3,3,2,7,6,3],[4,5,2,3,7,7,7,7],[0,1,2,3,2,7,6,2],[4,6,1,6,4,5,6,7],[0,6,3,6,4,5,6,3],[0,1,3,3,4,5,6,3],[0,5,2,5,4,4,5,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,1,3,7,5,6,7],[2,6,3,3,2,7,6,3],[4,5,2,3,7,7,7,7],[0,1,2,3,2,7,6,2],[4,6,1,6,4,5,6,7],[0,6,3,6,4,5,6,3],[0,1,3,3,4,5,6,3],[0,5,2,5,4,4,5,7]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2702] [2441] :=
    ⟨Fin 8, «FinitePoly [[1,5,1,3,7,5,6,7],[2,6,3,3,2,7,6,3],[4,5,2,3,7,7,7,7],[0,1,2,3,2,7,6,2],[4,6,1,6,4,5,6,7],[0,6,3,6,4,5,6,3],[0,1,3,3,4,5,6,3],[0,5,2,5,4,4,5,7]]», by decideFin!⟩
