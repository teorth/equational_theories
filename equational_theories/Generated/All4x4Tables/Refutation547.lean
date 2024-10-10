
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,4,6,0,5,3],[3,1,6,4,5,2,0],[2,1,4,3,0,6,5],[2,1,4,3,0,5,6],[2,1,4,5,0,3,6],[2,1,4,3,0,5,6],[2,1,4,3,0,5,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,4,6,0,5,3],[3,1,6,4,5,2,0],[2,1,4,3,0,6,5],[2,1,4,3,0,5,6],[2,1,4,5,0,3,6],[2,1,4,3,0,5,6],[2,1,4,3,0,5,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[2,1,4,6,0,5,3],[3,1,6,4,5,2,0],[2,1,4,3,0,6,5],[2,1,4,3,0,5,6],[2,1,4,5,0,3,6],[2,1,4,3,0,5,6],[2,1,4,3,0,5,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,4,6,0,5,3],[3,1,6,4,5,2,0],[2,1,4,3,0,6,5],[2,1,4,3,0,5,6],[2,1,4,5,0,3,6],[2,1,4,3,0,5,6],[2,1,4,3,0,5,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [65, 1491] [872, 879, 1518, 3915, 4118] :=
    ⟨Fin 7, «FinitePoly [[2,1,4,6,0,5,3],[3,1,6,4,5,2,0],[2,1,4,3,0,6,5],[2,1,4,3,0,5,6],[2,1,4,5,0,3,6],[2,1,4,3,0,5,6],[2,1,4,3,0,5,6]]», by decideFin!⟩
