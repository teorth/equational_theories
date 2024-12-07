
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,5,1,2,2],[2,4,1,0,5,1],[3,2,4,2,3,0],[5,0,3,4,2,3],[5,1,2,3,5,5],[1,5,0,5,1,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,3,5,1,2,2],[2,4,1,0,5,1],[3,2,4,2,3,0],[5,0,3,4,2,3],[5,1,2,3,5,5],[1,5,0,5,1,4]]» : Magma (Fin 6) where
  op := finOpTable "[[1,3,5,1,2,2],[2,4,1,0,5,1],[3,2,4,2,3,0],[5,0,3,4,2,3],[5,1,2,3,5,5],[1,5,0,5,1,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,3,5,1,2,2],[2,4,1,0,5,1],[3,2,4,2,3,0],[5,0,3,4,2,3],[5,1,2,3,5,5],[1,5,0,5,1,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1922] [1838, 4065, 4293, 4636] :=
    ⟨Fin 6, «All4x4Tables [[1,3,5,1,2,2],[2,4,1,0,5,1],[3,2,4,2,3,0],[5,0,3,4,2,3],[5,1,2,3,5,5],[1,5,0,5,1,4]]», Finite.of_fintype _, by decideFin!⟩
