
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,2,4,5,1,4],[5,1,6,2,0,4,3],[0,3,0,6,3,3,1],[3,6,1,3,6,6,2],[1,5,4,5,4,0,5],[4,0,5,0,1,5,0],[6,2,3,1,2,2,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,4,2,4,5,1,4],[5,1,6,2,0,4,3],[0,3,0,6,3,3,1],[3,6,1,3,6,6,2],[1,5,4,5,4,0,5],[4,0,5,0,1,5,0],[6,2,3,1,2,2,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[2,4,2,4,5,1,4],[5,1,6,2,0,4,3],[0,3,0,6,3,3,1],[3,6,1,3,6,6,2],[1,5,4,5,4,0,5],[4,0,5,0,1,5,0],[6,2,3,1,2,2,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,4,2,4,5,1,4],[5,1,6,2,0,4,3],[0,3,0,6,3,3,1],[3,6,1,3,6,6,2],[1,5,4,5,4,0,5],[4,0,5,0,1,5,0],[6,2,3,1,2,2,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [206, 1648] [2444] :=
    ⟨Fin 7, «FinitePoly [[2,4,2,4,5,1,4],[5,1,6,2,0,4,3],[0,3,0,6,3,3,1],[3,6,1,3,6,6,2],[1,5,4,5,4,0,5],[4,0,5,0,1,5,0],[6,2,3,1,2,2,6]]», Finite.of_fintype _, by decideFin!⟩
