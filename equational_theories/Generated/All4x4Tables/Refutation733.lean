
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,6,3,2,4,0,1],[3,2,6,4,0,1,5],[6,1,5,3,4,2,0],[0,1,4,5,2,3,6],[2,3,0,1,5,4,6],[0,1,2,3,6,5,4],[3,5,1,4,0,6,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,6,3,2,4,0,1],[3,2,6,4,0,1,5],[6,1,5,3,4,2,0],[0,1,4,5,2,3,6],[2,3,0,1,5,4,6],[0,1,2,3,6,5,4],[3,5,1,4,0,6,2]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[5,6,3,2,4,0,1],[3,2,6,4,0,1,5],[6,1,5,3,4,2,0],[0,1,4,5,2,3,6],[2,3,0,1,5,4,6],[0,1,2,3,6,5,4],[3,5,1,4,0,6,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,6,3,2,4,0,1],[3,2,6,4,0,1,5],[6,1,5,3,4,2,0],[0,1,4,5,2,3,6],[2,3,0,1,5,4,6],[0,1,2,3,6,5,4],[3,5,1,4,0,6,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [910] [513, 1861, 4290] :=
    ⟨Fin 7, «FinitePoly [[5,6,3,2,4,0,1],[3,2,6,4,0,1,5],[6,1,5,3,4,2,0],[0,1,4,5,2,3,6],[2,3,0,1,5,4,6],[0,1,2,3,6,5,4],[3,5,1,4,0,6,2]]», by decideFin!⟩
