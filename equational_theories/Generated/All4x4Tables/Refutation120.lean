
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,2,2],[0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[2,2,2],[0,0,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[2,2,2],[0,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[2,2,2],[0,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2052, 3466] [255, 3459, 3467, 3468, 3521, 3522, 3659, 3862, 4065, 4269, 4270, 4283, 4284, 4380, 4583, 4598, 4631] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[2,2,2],[0,0,0]]», Finite.of_fintype _, by decideFin!⟩
