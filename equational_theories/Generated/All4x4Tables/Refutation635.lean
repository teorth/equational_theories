
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,4,3,4,4],[0,0,0,0,0,0],[1,1,1,1,1,1],[2,5,2,5,5,5],[5,5,2,5,5,5],[1,1,1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,4,3,4,4],[0,0,0,0,0,0],[1,1,1,1,1,1],[2,5,2,5,5,5],[5,5,2,5,5,5],[1,1,1,1,1,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[3,3,4,3,4,4],[0,0,0,0,0,0],[1,1,1,1,1,1],[2,5,2,5,5,5],[5,5,2,5,5,5],[1,1,1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,4,3,4,4],[0,0,0,0,0,0],[1,1,1,1,1,1],[2,5,2,5,5,5],[5,5,2,5,5,5],[1,1,1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3081] [4584] :=
    ⟨Fin 6, «FinitePoly [[3,3,4,3,4,4],[0,0,0,0,0,0],[1,1,1,1,1,1],[2,5,2,5,5,5],[5,5,2,5,5,5],[1,1,1,1,1,1]]», by decideFin!⟩
