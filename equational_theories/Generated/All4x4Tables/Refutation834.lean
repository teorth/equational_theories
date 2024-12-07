
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3,2],[2,4,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,3,2],[2,4,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]» : Magma (Fin 5) where
  op := finOpTable "[[3,2,3,3,2],[2,4,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,3,2],[2,4,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4418] [4270, 4272, 4284, 4290, 4343, 4470, 4472, 4473, 4479, 4480, 4482] :=
    ⟨Fin 5, «All4x4Tables [[3,2,3,3,2],[2,4,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
