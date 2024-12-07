
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1687] [1038, 1055, 1225, 1238, 1248, 1634, 1644, 1654, 1691, 1837, 1847, 1857, 1884, 1921, 3306, 3309, 3343, 3346, 3353, 3880, 3897, 4067, 4080, 4090, 4118, 4128, 4155, 4284, 4291, 4320, 4635, 4666] :=
    ⟨Fin 4, «All4x4Tables [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
