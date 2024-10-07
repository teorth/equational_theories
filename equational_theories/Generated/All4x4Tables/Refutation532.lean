
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,0,3],[3,1,3,1,3],[2,0,2,4,2],[3,3,3,3,3],[4,0,4,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,0,3],[3,1,3,1,3],[2,0,2,4,2],[3,3,3,3,3],[4,0,4,2,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,0,0,3],[3,1,3,1,3],[2,0,2,4,2],[3,3,3,3,3],[4,0,4,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,0,3],[3,1,3,1,3],[2,0,2,4,2],[3,3,3,3,3],[4,0,4,2,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1233] [825, 829] :=
    ⟨Fin 5, «FinitePoly [[0,2,0,0,3],[3,1,3,1,3],[2,0,2,4,2],[3,3,3,3,3],[4,0,4,2,4]]», by decideFin!⟩
