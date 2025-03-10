
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [420, 501, 1435] [151, 203, 1427, 1428, 1429, 1444, 1445, 1629, 1832, 3253, 3456, 4314] :=
    ⟨Fin 4, «All4x4Tables [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]», Finite.of_fintype _, by decideFin!⟩
