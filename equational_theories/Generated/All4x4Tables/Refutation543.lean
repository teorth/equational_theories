
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,1,5,1,5],[2,0,2,0,2,0],[3,1,3,1,3,1],[4,2,4,2,4,2],[5,3,5,3,5,3],[0,4,0,4,0,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,1,5,1,5],[2,0,2,0,2,0],[3,1,3,1,3,1],[4,2,4,2,4,2],[5,3,5,3,5,3],[0,4,0,4,0,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,5,1,5,1,5],[2,0,2,0,2,0],[3,1,3,1,3,1],[4,2,4,2,4,2],[5,3,5,3,5,3],[0,4,0,4,0,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,1,5,1,5],[2,0,2,0,2,0],[3,1,3,1,3,1],[4,2,4,2,4,2],[5,3,5,3,5,3],[0,4,0,4,0,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [161] [3050, 4585] :=
    ⟨Fin 6, «FinitePoly [[1,5,1,5,1,5],[2,0,2,0,2,0],[3,1,3,1,3,1],[4,2,4,2,4,2],[5,3,5,3,5,3],[0,4,0,4,0,4]]», by decideFin!⟩
