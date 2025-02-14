
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,1],[3,1,0,2],[1,0,3,2],[0,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,0,1],[3,1,0,2],[1,0,3,2],[0,3,1,0]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,1],[3,1,0,2],[1,0,3,2],[0,3,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,0,1],[3,1,0,2],[1,0,3,2],[0,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2134] [1832, 2050, 2053, 2087, 2124, 2127, 3258, 3261, 3306, 3309, 3353, 3456, 3877, 3887, 3955, 3962, 4067, 4083, 4121, 4158, 4284, 4380, 4599, 4635] :=
    ⟨Fin 4, «All4x4Tables [[2,1,0,1],[3,1,0,2],[1,0,3,2],[0,3,1,0]]», Finite.of_fintype _, by decideFin!⟩
