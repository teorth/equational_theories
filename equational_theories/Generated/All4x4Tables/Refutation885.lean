
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]» : Magma (Fin 6) where
  op := finOpTable "[[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4164] [3308, 3352] :=
    ⟨Fin 6, «All4x4Tables [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]», Finite.of_fintype _, by decideFin!⟩
