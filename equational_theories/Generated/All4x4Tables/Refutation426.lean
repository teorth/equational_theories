
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2044] [255, 307, 2053, 2060, 2644, 2847, 3259, 3308, 3319, 3459, 3462, 3511, 3518, 3522, 4283, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]», by decideFin!⟩
