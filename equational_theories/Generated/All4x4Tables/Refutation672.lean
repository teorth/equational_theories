
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,4,1,0,5,2],[2,1,3,4,0,5],[5,0,4,1,2,3],[0,2,5,3,1,4],[1,3,2,5,4,0],[4,5,0,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,4,1,0,5,2],[2,1,3,4,0,5],[5,0,4,1,2,3],[0,2,5,3,1,4],[1,3,2,5,4,0],[4,5,0,2,3,1]]» : Magma (Fin 6) where
  op := finOpTable "[[3,4,1,0,5,2],[2,1,3,4,0,5],[5,0,4,1,2,3],[0,2,5,3,1,4],[1,3,2,5,4,0],[4,5,0,2,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,4,1,0,5,2],[2,1,3,4,0,5],[5,0,4,1,2,3],[0,2,5,3,1,4],[1,3,2,5,4,0],[4,5,0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1312, 2241, 3355, 4154] [1451, 2043, 3306, 4131] :=
    ⟨Fin 6, «All4x4Tables [[3,4,1,0,5,2],[2,1,3,4,0,5],[5,0,4,1,2,3],[0,2,5,3,1,4],[1,3,2,5,4,0],[4,5,0,2,3,1]]», Finite.of_fintype _, by decideFin!⟩
