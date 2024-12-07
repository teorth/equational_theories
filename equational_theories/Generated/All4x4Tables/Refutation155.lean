
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,1],[0,2,1],[1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,1],[0,2,1],[1,1,1]]» : Magma (Fin 3) where
  op := finOpTable "[[1,0,1],[0,2,1],[1,1,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,1],[0,2,1],[1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1482, 1694, 1860, 2053, 2125, 2127] [151, 1427, 1428, 1429, 1631, 1634, 1637, 1837, 1847, 1857, 1931, 2050, 2087, 2124, 2134, 3258, 3261, 3309, 3457, 3462, 3521, 3877, 3880, 3887, 3890, 3952, 4067, 4083, 4093, 4121, 4284, 4314, 4591, 4599, 4606] :=
    ⟨Fin 3, «All4x4Tables [[1,0,1],[0,2,1],[1,1,1]]», Finite.of_fintype _, by decideFin!⟩
