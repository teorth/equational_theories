
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1353] [127, 179, 1288, 1325, 2063, 2137, 3925, 3952, 4606] :=
    ⟨Fin 4, «FinitePoly [[1,0,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]», by decideFin!⟩
