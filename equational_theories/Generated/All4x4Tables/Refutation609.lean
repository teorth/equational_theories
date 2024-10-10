
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[5,2,3,3,5,5,5],[4,1,3,3,4,5,6],[0,2,2,2,4,5,6],[0,1,3,3,4,5,6],[5,1,2,3,5,5,5],[6,1,2,3,6,6,6],[0,1,2,3,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[5,2,3,3,5,5,5],[4,1,3,3,4,5,6],[0,2,2,2,4,5,6],[0,1,3,3,4,5,6],[5,1,2,3,5,5,5],[6,1,2,3,6,6,6],[0,1,2,3,4,4,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[5,2,3,3,5,5,5],[4,1,3,3,4,5,6],[0,2,2,2,4,5,6],[0,1,3,3,4,5,6],[5,1,2,3,5,5,5],[6,1,2,3,6,6,6],[0,1,2,3,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[5,2,3,3,5,5,5],[4,1,3,3,4,5,6],[0,2,2,2,4,5,6],[0,1,3,3,4,5,6],[5,1,2,3,5,5,5],[6,1,2,3,6,6,6],[0,1,2,3,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2683] [2855, 3306] :=
    ⟨Fin 7, «FinitePoly [[5,2,3,3,5,5,5],[4,1,3,3,4,5,6],[0,2,2,2,4,5,6],[0,1,3,3,4,5,6],[5,1,2,3,5,5,5],[6,1,2,3,6,6,6],[0,1,2,3,4,4,4]]», by decideFin!⟩
