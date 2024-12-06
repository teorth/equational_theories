
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [162, 1447, 3089] [3058, 3075, 4073, 4121, 4599] :=
    ⟨Fin 4, «All4x4Tables [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]», Finite.of_fintype _, by decideFin!⟩
