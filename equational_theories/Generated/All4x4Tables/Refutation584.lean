
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2260, 3317] [160, 359, 1454, 1455, 2264, 3318, 3319, 3519, 3521, 3659, 3862, 4314] :=
    ⟨Fin 4, «All4x4Tables [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]», Finite.of_fintype _, by decideFin!⟩
