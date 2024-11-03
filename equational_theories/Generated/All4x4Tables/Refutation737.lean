
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,6,1,5,3,4],[5,5,1,6,0,5,5],[4,3,4,4,4,2,0],[2,0,2,2,2,4,3],[3,4,3,3,3,0,2],[6,6,0,5,1,6,6],[1,1,5,0,6,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,6,1,5,3,4],[5,5,1,6,0,5,5],[4,3,4,4,4,2,0],[2,0,2,2,2,4,3],[3,4,3,3,3,0,2],[6,6,0,5,1,6,6],[1,1,5,0,6,1,1]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,6,1,5,3,4],[5,5,1,6,0,5,5],[4,3,4,4,4,2,0],[2,0,2,2,2,4,3],[3,4,3,3,3,0,2],[6,6,0,5,1,6,6],[1,1,5,0,6,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,6,1,5,3,4],[5,5,1,6,0,5,5],[4,3,4,4,4,2,0],[2,0,2,2,2,4,3],[3,4,3,3,3,0,2],[6,6,0,5,1,6,6],[1,1,5,0,6,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2653] [3459] :=
    ⟨Fin 7, «FinitePoly [[0,2,6,1,5,3,4],[5,5,1,6,0,5,5],[4,3,4,4,4,2,0],[2,0,2,2,2,4,3],[3,4,3,3,3,0,2],[6,6,0,5,1,6,6],[1,1,5,0,6,1,1]]», Finite.of_fintype _, by decideFin!⟩
