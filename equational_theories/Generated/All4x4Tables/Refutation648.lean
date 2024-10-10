
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,3,1,3],[4,0,4,0,4],[0,1,2,3,4],[4,2,2,2,4],[2,3,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,3,1,3],[4,0,4,0,4],[0,1,2,3,4],[4,2,2,2,4],[2,3,2,3,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,3,3,1,3],[4,0,4,0,4],[0,1,2,3,4],[4,2,2,2,4],[2,3,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,3,1,3],[4,0,4,0,4],[0,1,2,3,4],[4,2,2,2,4],[2,3,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3197] [2644, 3456] :=
    ⟨Fin 5, «FinitePoly [[1,3,3,1,3],[4,0,4,0,4],[0,1,2,3,4],[4,2,2,2,4],[2,3,2,3,2]]», by decideFin!⟩
