
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3,3],[2,4,2,4,4],[0,0,0,0,0],[4,4,2,2,4],[0,0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,1,3,3,3],[2,4,2,4,4],[0,0,0,0,0],[4,4,2,2,4],[0,0,0,0,0]]» : Magma (Fin 5) where
  op := finOpTable "[[3,1,3,3,3],[2,4,2,4,4],[0,0,0,0,0],[4,4,2,2,4],[0,0,0,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,1,3,3,3],[2,4,2,4,4],[0,0,0,0,0],[4,4,2,2,4],[0,0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [266] [4584] :=
    ⟨Fin 5, «All4x4Tables [[3,1,3,3,3],[2,4,2,4,4],[0,0,0,0,0],[4,4,2,2,4],[0,0,0,0,0]]», Finite.of_fintype _, by decideFin!⟩
