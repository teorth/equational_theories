
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1,2],[3,3,4,0,4],[3,3,3,0,3],[3,3,2,1,2],[1,1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1,2],[3,3,4,0,4],[3,3,3,0,3],[3,3,2,1,2],[1,1,1,1,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,2,1,2],[3,3,4,0,4],[3,3,3,0,3],[3,3,2,1,2],[1,1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1,2],[3,3,4,0,4],[3,3,3,0,3],[3,3,2,1,2],[1,1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1672] [3253] :=
    ⟨Fin 5, «FinitePoly [[1,2,2,1,2],[3,3,4,0,4],[3,3,3,0,3],[3,3,2,1,2],[1,1,1,1,1]]», by decideFin!⟩
