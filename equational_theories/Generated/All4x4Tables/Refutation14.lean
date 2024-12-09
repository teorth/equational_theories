
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]» : Magma (Fin 7) where
  op := finOpTable "[[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1313, 1315, 1322] [49, 65, 73, 99, 151, 203, 255, 411, 706, 713, 1020, 1238, 1241, 1248, 1251, 1278, 1285, 1286, 1288, 1629, 1832, 2035, 2301, 2504, 2531, 2644, 2866, 3069, 3106, 3253, 3545, 3659, 3862, 4065, 4275, 4283, 4320, 4343, 4398, 4405, 4470, 4482, 4587, 4606, 4608] :=
    ⟨Fin 7, «All4x4Tables [[0,2,3,1,6,4,5],[1,4,5,2,0,3,6],[2,3,6,4,1,5,0],[3,6,1,5,4,0,2],[4,5,0,3,2,6,1],[5,0,2,6,3,1,4],[6,1,4,0,5,2,3]]», Finite.of_fintype _, by decideFin!⟩
