
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,2,5,4],[2,3,4,5,0,1],[5,4,1,0,3,2],[0,1,2,3,4,5],[3,2,5,4,1,0],[4,5,0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,3,2,5,4],[2,3,4,5,0,1],[5,4,1,0,3,2],[0,1,2,3,4,5],[3,2,5,4,1,0],[4,5,0,1,2,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,0,3,2,5,4],[2,3,4,5,0,1],[5,4,1,0,3,2],[0,1,2,3,4,5],[3,2,5,4,1,0],[4,5,0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,3,2,5,4],[2,3,4,5,0,1],[5,4,1,0,3,2],[0,1,2,3,4,5],[3,2,5,4,1,0],[4,5,0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1898, 2710] [1629, 3050] :=
    ⟨Fin 6, «FinitePoly [[1,0,3,2,5,4],[2,3,4,5,0,1],[5,4,1,0,3,2],[0,1,2,3,4,5],[3,2,5,4,1,0],[4,5,0,1,2,3]]», by decideFin!⟩
