
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2770] [2238, 2466, 3509] :=
    ⟨Fin 4, «All4x4Tables [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]», Finite.of_fintype _, by decideFin!⟩
