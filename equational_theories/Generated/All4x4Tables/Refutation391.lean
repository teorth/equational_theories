
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]» : Magma (Fin 4) where
  op := finOpTable "[[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2739] [2290, 2300, 2303, 2327, 2659, 3464] :=
    ⟨Fin 4, «All4x4Tables [[0,0,2,3],[2,2,2,3],[0,1,2,2],[0,1,1,0]]», Finite.of_fintype _, by decideFin!⟩
