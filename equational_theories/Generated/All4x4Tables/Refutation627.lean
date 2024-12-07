
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [53, 273, 281, 1117, 1152, 1155, 2538] [99, 203, 411, 614, 817, 1028, 1045, 1629, 1832, 2449, 2466, 2506, 3050, 3253, 3456, 3659, 3862, 4065, 4270, 4275, 4380, 4656] :=
    ⟨Fin 4, «All4x4Tables [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]», Finite.of_fintype _, by decideFin!⟩
