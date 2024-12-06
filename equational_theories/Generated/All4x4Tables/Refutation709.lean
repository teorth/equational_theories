
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3008] [429, 511, 632, 707, 817, 1020, 1223, 2238, 2441, 2644, 2865, 2940, 3068, 4290, 4435, 4605] :=
    ⟨Fin 5, «All4x4Tables [[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]», Finite.of_fintype _, by decideFin!⟩
