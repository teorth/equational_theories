
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,4,3,3,4,2],[2,1,2,4,4,2],[0,1,2,4,0,5],[4,1,2,3,0,5],[5,1,2,3,4,2],[0,1,3,4,0,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,4,3,3,4,2],[2,1,2,4,4,2],[0,1,2,4,0,5],[4,1,2,3,0,5],[5,1,2,3,4,2],[0,1,3,4,0,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,4,3,3,4,2],[2,1,2,4,4,2],[0,1,2,4,0,5],[4,1,2,3,0,5],[5,1,2,3,4,2],[0,1,3,4,0,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,4,3,3,4,2],[2,1,2,4,4,2],[0,1,2,4,0,5],[4,1,2,3,0,5],[5,1,2,3,4,2],[0,1,3,4,0,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2584] [2862] :=
    ⟨Fin 6, «FinitePoly [[0,4,3,3,4,2],[2,1,2,4,4,2],[0,1,2,4,0,5],[4,1,2,3,0,5],[5,1,2,3,4,2],[0,1,3,4,0,5]]», by decideFin!⟩
