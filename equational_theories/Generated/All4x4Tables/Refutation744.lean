
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3555] [3862] :=
    ⟨Fin 7, «FinitePoly [[1,2,6,5,3,4,1],[6,1,2,1,1,5,1],[3,2,2,2,6,4,5],[4,1,2,3,3,5,1],[5,1,5,3,4,4,6],[3,5,6,5,4,5,5],[2,1,4,1,6,5,6]]», by decideFin!⟩
