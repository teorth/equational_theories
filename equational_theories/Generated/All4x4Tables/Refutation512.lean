
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,3],[3,3,3,1],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,1,3],[3,3,3,1],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,1,3],[3,3,3,1],[0,1,2,3],[0,1,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,1,3],[3,3,3,1],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2964] [2238, 2459, 2503, 2872, 2902, 2909, 3075, 3112, 3253, 3677, 3862] :=
    ⟨Fin 4, «All4x4Tables [[2,1,1,3],[3,3,3,1],[0,1,2,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
