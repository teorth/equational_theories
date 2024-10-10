
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [100, 847, 1052] [105, 107, 1223, 4598] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,1,2],[2,2,0,3],[3,3,1,0]]», by decideFin!⟩
