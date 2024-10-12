
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4364] [4358, 4362, 4369, 4380] :=
    ⟨Fin 8, «FinitePoly [[1,4,1,3,5,3,4,5],[7,5,3,3,3,3,3,3],[6,4,6,3,3,3,4,5],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[5,3,5,3,3,3,3,3],[7,5,3,3,3,3,3,3],[5,3,5,3,3,3,3,3]]», by decideFin!⟩
