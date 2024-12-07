
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [655] [417, 419, 427, 429, 617, 639, 825, 833, 1023, 1026, 1038, 1045, 1223, 3259, 3261, 3306, 3308, 4598] :=
    ⟨Fin 4, «All4x4Tables [[1,0,3,1],[3,1,0,3],[1,2,1,0],[2,3,2,1]]», Finite.of_fintype _, by decideFin!⟩
