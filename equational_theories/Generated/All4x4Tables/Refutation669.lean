
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,5,3,4],[4,2,1,3,5,0],[3,2,1,4,0,5],[4,2,1,3,5,0],[5,2,1,0,4,3],[3,2,1,4,0,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,5,3,4],[4,2,1,3,5,0],[3,2,1,4,0,5],[4,2,1,3,5,0],[5,2,1,0,4,3],[3,2,1,4,0,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,2,1,5,3,4],[4,2,1,3,5,0],[3,2,1,4,0,5],[4,2,1,3,5,0],[5,2,1,0,4,3],[3,2,1,4,0,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,5,3,4],[4,2,1,3,5,0],[3,2,1,4,0,5],[4,2,1,3,5,0],[5,2,1,0,4,3],[3,2,1,4,0,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [124, 1924] [159, 375] :=
    ⟨Fin 6, «FinitePoly [[0,2,1,5,3,4],[4,2,1,3,5,0],[3,2,1,4,0,5],[4,2,1,3,5,0],[5,2,1,0,4,3],[3,2,1,4,0,5]]», Finite.of_fintype _, by decideFin!⟩
