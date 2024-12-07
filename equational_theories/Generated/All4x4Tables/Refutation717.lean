
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [194] [411, 4275] :=
    ⟨Fin 6, «All4x4Tables [[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4],[1,2,3,4,5,0],[5,0,1,2,3,4]]», Finite.of_fintype _, by decideFin!⟩
