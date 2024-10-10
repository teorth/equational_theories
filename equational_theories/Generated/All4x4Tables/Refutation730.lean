
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,0,0,0],[1,4,1,4,5,1],[0,0,2,2,2,2],[3,4,3,4,5,3],[4,4,4,4,5,3],[5,4,5,4,5,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,0,0,0],[1,4,1,4,5,1],[0,0,2,2,2,2],[3,4,3,4,5,3],[4,4,4,4,5,3],[5,4,5,4,5,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,2,2,0,0,0],[1,4,1,4,5,1],[0,0,2,2,2,2],[3,4,3,4,5,3],[4,4,4,4,5,3],[5,4,5,4,5,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,0,0,0],[1,4,1,4,5,1],[0,0,2,2,2,2],[3,4,3,4,5,3],[4,4,4,4,5,3],[5,4,5,4,5,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [856] [378, 629, 632, 832] :=
    ⟨Fin 6, «FinitePoly [[0,2,2,0,0,0],[1,4,1,4,5,1],[0,0,2,2,2,2],[3,4,3,4,5,3],[4,4,4,4,5,3],[5,4,5,4,5,3]]», by decideFin!⟩
