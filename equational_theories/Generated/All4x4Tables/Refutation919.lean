
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,5,2,4],[0,1,2,3,4,5],[5,3,1,4,0,3],[4,4,0,1,5,2],[3,5,5,2,1,0],[2,0,4,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,3,5,2,4],[0,1,2,3,4,5],[5,3,1,4,0,3],[4,4,0,1,5,2],[3,5,5,2,1,0],[2,0,4,0,3,1]]» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,5,2,4],[0,1,2,3,4,5],[5,3,1,4,0,3],[4,4,0,1,5,2],[3,5,5,2,1,0],[2,0,4,0,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,3,5,2,4],[0,1,2,3,4,5],[5,3,1,4,0,3],[4,4,0,1,5,2],[3,5,5,2,1,0],[2,0,4,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3113] [1632, 1654, 1832, 2449, 2457, 2470, 3079] :=
    ⟨Fin 6, «All4x4Tables [[1,2,3,5,2,4],[0,1,2,3,4,5],[5,3,1,4,0,3],[4,4,0,1,5,2],[3,5,5,2,1,0],[2,0,4,0,3,1]]», Finite.of_fintype _, by decideFin!⟩
