
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [124, 1924] [1109, 1322, 1728, 4118] :=
    ⟨Fin 7, «FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]», by decideFin!⟩
