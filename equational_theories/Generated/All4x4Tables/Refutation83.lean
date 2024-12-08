
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[1,0,1],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1],[1,0,1],[2,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[1,0,1],[2,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1],[1,0,1],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [11, 105, 427, 1045, 1647, 1840, 3282, 3891, 3962] [108, 1023, 1025, 1038, 1048, 1224, 1226, 1229, 1231, 1238, 1242, 1251, 1252, 3279, 3685, 3687, 3881, 3888, 3895, 4065, 4269, 4314, 4591, 4598, 4606, 4608, 4631, 4647] :=
    ⟨Fin 3, «All4x4Tables [[0,2,1],[1,0,1],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
