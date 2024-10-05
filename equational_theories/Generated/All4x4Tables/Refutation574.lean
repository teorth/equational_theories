
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [261, 2061] [2660, 2873] :=
    ⟨Fin 7, «FinitePoly [[3,2,3,3,3,3,3],[1,1,1,1,1,1,1],[6,4,2,2,5,2,2],[4,6,4,4,4,4,4],[0,5,0,0,0,0,0],[5,3,5,6,2,5,5],[2,0,6,5,6,6,6]]», by decideFin!⟩
