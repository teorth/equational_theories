
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,2,3,0],[2,1,3,4,2],[0,3,1,2,4],[0,2,4,3,1],[3,4,2,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,4,2,3,0],[2,1,3,4,2],[0,3,1,2,4],[0,2,4,3,1],[3,4,2,1,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,4,2,3,0],[2,1,3,4,2],[0,3,1,2,4],[0,2,4,3,1],[3,4,2,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,4,2,3,0],[2,1,3,4,2],[0,3,1,2,4],[0,2,4,3,1],[3,4,2,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2939] [99, 2035] :=
    ⟨Fin 5, «FinitePoly [[1,4,2,3,0],[2,1,3,4,2],[0,3,1,2,4],[0,2,4,3,1],[3,4,2,1,3]]», Finite.of_fintype _, by decideFin!⟩
