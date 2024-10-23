
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,6,6,2,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[4,1,3,6,4,4,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[0,1,2,3,4,5,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,6,6,2,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[4,1,3,6,4,4,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[0,1,2,3,4,5,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,6,6,2,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[4,1,3,6,4,4,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[0,1,2,3,4,5,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,6,6,2,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[4,1,3,6,4,4,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[0,1,2,3,4,5,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2778] [2238, 4065] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,6,6,2,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[4,1,3,6,4,4,6],[4,6,2,3,6,5,6],[0,1,5,6,4,6,6],[0,1,2,3,4,5,6]]», Finite.of_fintype _, by decideFin!⟩
