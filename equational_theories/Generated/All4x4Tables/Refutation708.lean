
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,2,3,3,0],[3,2,1,3,0],[4,2,1,3,3],[4,2,1,3,0],[4,3,1,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,2,3,3,0],[3,2,1,3,0],[4,2,1,3,3],[4,2,1,3,0],[4,3,1,3,0]]» : Magma (Fin 5) where
  op := finOpTable "[[4,2,3,3,0],[3,2,1,3,0],[4,2,1,3,3],[4,2,1,3,0],[4,3,1,3,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,2,3,3,0],[3,2,1,3,0],[4,2,1,3,3],[4,2,1,3,0],[4,3,1,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1904] [1038, 1225, 1644, 1654, 1857, 3306, 3309, 3343, 3346, 3880, 4067, 4118, 4128, 4155, 4284, 4291, 4320] :=
    ⟨Fin 5, «All4x4Tables [[4,2,3,3,0],[3,2,1,3,0],[4,2,1,3,3],[4,2,1,3,0],[4,3,1,3,0]]», Finite.of_fintype _, by decideFin!⟩
