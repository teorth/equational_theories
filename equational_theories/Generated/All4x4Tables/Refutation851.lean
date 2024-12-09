
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,0,4,6,2],[3,2,5,3,4,1,2],[0,2,5,4,4,6,2],[3,2,5,3,3,6,2],[0,2,5,4,4,6,2],[0,2,5,0,4,1,2],[0,2,5,4,4,6,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,5,0,4,6,2],[3,2,5,3,4,1,2],[0,2,5,4,4,6,2],[3,2,5,3,3,6,2],[0,2,5,4,4,6,2],[0,2,5,0,4,1,2],[0,2,5,4,4,6,2]]» : Magma (Fin 7) where
  op := finOpTable "[[0,2,5,0,4,6,2],[3,2,5,3,4,1,2],[0,2,5,4,4,6,2],[3,2,5,3,3,6,2],[0,2,5,4,4,6,2],[0,2,5,0,4,1,2],[0,2,5,4,4,6,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,5,0,4,6,2],[3,2,5,3,4,1,2],[0,2,5,4,4,6,2],[3,2,5,3,3,6,2],[0,2,5,4,4,6,2],[0,2,5,0,4,1,2],[0,2,5,4,4,6,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [645] [845, 1426, 3862] :=
    ⟨Fin 7, «All4x4Tables [[0,2,5,0,4,6,2],[3,2,5,3,4,1,2],[0,2,5,4,4,6,2],[3,2,5,3,3,6,2],[0,2,5,4,4,6,2],[0,2,5,0,4,1,2],[0,2,5,4,4,6,2]]», Finite.of_fintype _, by decideFin!⟩
