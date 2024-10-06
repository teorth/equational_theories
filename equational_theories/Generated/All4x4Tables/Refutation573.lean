
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,1,1,4,1],[2,2,5,2,2,5],[3,0,0,3,0,0],[4,1,4,4,1,4],[5,5,2,5,5,2],[0,3,3,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,4,1,1,4,1],[2,2,5,2,2,5],[3,0,0,3,0,0],[4,1,4,4,1,4],[5,5,2,5,5,2],[0,3,3,0,3,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,4,1,1,4,1],[2,2,5,2,2,5],[3,0,0,3,0,0],[4,1,4,4,1,4],[5,5,2,5,5,2],[0,3,3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,4,1,1,4,1],[2,2,5,2,2,5],[3,0,0,3,0,0],[4,1,4,4,1,4],[5,5,2,5,5,2],[0,3,3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2045, 2883] [255, 2060, 2644, 2865, 2875, 3253, 3518, 3519, 3521, 3522, 4598, 4656] :=
    ⟨Fin 6, «FinitePoly [[1,4,1,1,4,1],[2,2,5,2,2,5],[3,0,0,3,0,0],[4,1,4,4,1,4],[5,5,2,5,5,2],[0,3,3,0,3,3]]», by decideFin!⟩
