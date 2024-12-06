
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,5,7,3,0,4,6],[2,3,4,6,7,5,1,0],[3,7,6,2,1,4,0,5],[7,3,0,6,2,5,1,4],[3,7,6,2,1,4,0,5],[2,3,4,6,7,5,1,0],[7,3,0,6,2,5,1,4],[1,2,5,7,3,0,4,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,5,7,3,0,4,6],[2,3,4,6,7,5,1,0],[3,7,6,2,1,4,0,5],[7,3,0,6,2,5,1,4],[3,7,6,2,1,4,0,5],[2,3,4,6,7,5,1,0],[7,3,0,6,2,5,1,4],[1,2,5,7,3,0,4,6]]» : Magma (Fin 8) where
  op := finOpTable "[[1,2,5,7,3,0,4,6],[2,3,4,6,7,5,1,0],[3,7,6,2,1,4,0,5],[7,3,0,6,2,5,1,4],[3,7,6,2,1,4,0,5],[2,3,4,6,7,5,1,0],[7,3,0,6,2,5,1,4],[1,2,5,7,3,0,4,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,5,7,3,0,4,6],[2,3,4,6,7,5,1,0],[3,7,6,2,1,4,0,5],[7,3,0,6,2,5,1,4],[3,7,6,2,1,4,0,5],[2,3,4,6,7,5,1,0],[7,3,0,6,2,5,1,4],[1,2,5,7,3,0,4,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [676] [1426, 3862, 4065] :=
    ⟨Fin 8, «All4x4Tables [[1,2,5,7,3,0,4,6],[2,3,4,6,7,5,1,0],[3,7,6,2,1,4,0,5],[7,3,0,6,2,5,1,4],[3,7,6,2,1,4,0,5],[2,3,4,6,7,5,1,0],[7,3,0,6,2,5,1,4],[1,2,5,7,3,0,4,6]]», Finite.of_fintype _, by decideFin!⟩
