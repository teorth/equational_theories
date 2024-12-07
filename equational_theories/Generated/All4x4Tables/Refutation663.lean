
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,4,5,6,3],[2,1,0,4,5,6,3],[2,3,0,6,1,5,4],[2,5,0,3,6,4,1],[2,6,0,1,4,3,5],[2,3,0,6,1,5,4],[2,4,0,5,3,1,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,0,4,5,6,3],[2,1,0,4,5,6,3],[2,3,0,6,1,5,4],[2,5,0,3,6,4,1],[2,6,0,1,4,3,5],[2,3,0,6,1,5,4],[2,4,0,5,3,1,6]]» : Magma (Fin 7) where
  op := finOpTable "[[2,1,0,4,5,6,3],[2,1,0,4,5,6,3],[2,3,0,6,1,5,4],[2,5,0,3,6,4,1],[2,6,0,1,4,3,5],[2,3,0,6,1,5,4],[2,4,0,5,3,1,6]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,0,4,5,6,3],[2,1,0,4,5,6,3],[2,3,0,6,1,5,4],[2,5,0,3,6,4,1],[2,6,0,1,4,3,5],[2,3,0,6,1,5,4],[2,4,0,5,3,1,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1119] [466, 1038, 1075, 1241, 1684, 1894, 2097, 3880, 3955, 4083, 4118, 4158] :=
    ⟨Fin 7, «All4x4Tables [[2,1,0,4,5,6,3],[2,1,0,4,5,6,3],[2,3,0,6,1,5,4],[2,5,0,3,6,4,1],[2,6,0,1,4,3,5],[2,3,0,6,1,5,4],[2,4,0,5,3,1,6]]», Finite.of_fintype _, by decideFin!⟩
