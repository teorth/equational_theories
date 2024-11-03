
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,6,4,0,6,0],[2,2,2,2,2,2,2],[3,3,3,3,3,3,3],[5,5,5,5,5,5,5],[4,4,0,6,4,0,4],[1,1,1,1,1,1,1],[6,6,4,0,6,4,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,6,4,0,6,0],[2,2,2,2,2,2,2],[3,3,3,3,3,3,3],[5,5,5,5,5,5,5],[4,4,0,6,4,0,4],[1,1,1,1,1,1,1],[6,6,4,0,6,4,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,0,6,4,0,6,0],[2,2,2,2,2,2,2],[3,3,3,3,3,3,3],[5,5,5,5,5,5,5],[4,4,0,6,4,0,4],[1,1,1,1,1,1,1],[6,6,4,0,6,4,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,6,4,0,6,0],[2,2,2,2,2,2,2],[3,3,3,3,3,3,3],[5,5,5,5,5,5,5],[4,4,0,6,4,0,4],[1,1,1,1,1,1,1],[6,6,4,0,6,4,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3059, 3069, 3076] [3522] :=
    ⟨Fin 7, «FinitePoly [[0,0,6,4,0,6,0],[2,2,2,2,2,2,2],[3,3,3,3,3,3,3],[5,5,5,5,5,5,5],[4,4,0,6,4,0,4],[1,1,1,1,1,1,1],[6,6,4,0,6,4,6]]», Finite.of_fintype _, by decideFin!⟩
