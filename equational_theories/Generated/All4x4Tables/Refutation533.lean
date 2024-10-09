
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1235] [1026, 1227, 1230, 1233, 1234, 1633, 2452, 3460, 3721, 3927, 4120, 4127, 4131, 4472, 4598] :=
    ⟨Fin 6, «FinitePoly [[0,5,3,0,5,0],[2,1,1,1,1,2],[3,4,2,2,2,3],[3,4,3,3,3,3],[4,3,3,4,4,3],[5,0,0,5,5,5]]», by decideFin!⟩
