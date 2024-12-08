
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [428] [825, 833, 838, 840, 1032, 1227, 1230, 1233, 1235, 1236, 1240, 1243, 1245, 1250, 1259, 1633, 2452, 2462, 3460, 3463, 3724, 3931, 4673] :=
    ⟨Fin 4, «All4x4Tables [[0,0,0,1],[1,1,0,1],[2,0,2,2],[2,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
