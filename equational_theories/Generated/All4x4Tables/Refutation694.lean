
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,2,3],[4,0,1,4,2],[4,3,2,2,2],[1,3,3,2,3],[4,0,4,4,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,2,3],[4,0,1,4,2],[4,3,2,2,2],[1,3,3,2,3],[4,0,4,4,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,3,0,2,3],[4,0,1,4,2],[4,3,2,2,2],[1,3,3,2,3],[4,0,4,4,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,2,3],[4,0,1,4,2],[4,3,2,2,2],[1,3,3,2,3],[4,0,4,4,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [443] [817] :=
    ⟨Fin 5, «FinitePoly [[1,3,0,2,3],[4,0,1,4,2],[4,3,2,2,2],[1,3,3,2,3],[4,0,4,4,2]]», by decideFin!⟩
