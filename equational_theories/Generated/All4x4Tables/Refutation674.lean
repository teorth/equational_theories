
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,3,5,2,0],[2,3,4,5,1,0],[5,0,4,2,1,3],[1,4,3,5,2,0],[5,4,0,1,2,3],[5,0,4,2,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,4,3,5,2,0],[2,3,4,5,1,0],[5,0,4,2,1,3],[1,4,3,5,2,0],[5,4,0,1,2,3],[5,0,4,2,1,3]]» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,5,2,0],[2,3,4,5,1,0],[5,0,4,2,1,3],[1,4,3,5,2,0],[5,4,0,1,2,3],[5,0,4,2,1,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,4,3,5,2,0],[2,3,4,5,1,0],[5,0,4,2,1,3],[1,4,3,5,2,0],[5,4,0,1,2,3],[5,0,4,2,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1370] [99, 151, 411, 1248, 1278, 1315, 2043, 2050, 2124, 3862, 4275, 4320, 4606, 4666] :=
    ⟨Fin 6, «All4x4Tables [[1,4,3,5,2,0],[2,3,4,5,1,0],[5,0,4,2,1,3],[1,4,3,5,2,0],[5,4,0,1,2,3],[5,0,4,2,1,3]]», Finite.of_fintype _, by decideFin!⟩
