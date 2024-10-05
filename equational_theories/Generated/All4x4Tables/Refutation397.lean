
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,1],[3,2,3,2],[2,3,0,3],[1,0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,1],[3,2,3,2],[2,3,0,3],[1,0,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,1],[3,2,3,2],[2,3,0,3],[1,0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,1],[3,2,3,2],[2,3,0,3],[1,0,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2853] [2644, 3259, 3459, 3462, 4358, 4585] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,1],[3,2,3,2],[2,3,0,3],[1,0,1,0]]», by decideFin!⟩
