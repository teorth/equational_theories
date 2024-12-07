
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,3,3],[3,3,2,2],[0,0,1,1],[1,1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,2,3,3],[3,3,2,2],[0,0,1,1],[1,1,0,0]]» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,3],[3,3,2,2],[0,0,1,1],[1,1,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,2,3,3],[3,3,2,2],[0,0,1,1],[1,1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2463] [151, 203, 1426, 2035, 2238, 2644, 3253, 3659, 3862] :=
    ⟨Fin 4, «All4x4Tables [[2,2,3,3],[3,3,2,2],[0,0,1,1],[1,1,0,0]]», Finite.of_fintype _, by decideFin!⟩
