
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [455, 658, 2688] [2647, 2662, 2853, 3261, 3306, 3464, 3509, 3511, 3665, 3865] :=
    ⟨Fin 4, «All4x4Tables [[2,0,0,1],[3,1,1,0],[0,2,2,3],[1,3,3,2]]», Finite.of_fintype _, by decideFin!⟩
