
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]» : Magma (Fin 6) where
  op := finOpTable "[[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4541] [4283, 4290, 4396, 4398, 4442, 4473, 4605, 4635] :=
    ⟨Fin 6, «All4x4Tables [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
