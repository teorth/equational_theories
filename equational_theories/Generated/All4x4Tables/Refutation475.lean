
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[2,0,3,1],[2,3,1,0],[1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,0,1],[2,0,3,1],[2,3,1,0],[1,3,0,2]]» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,1],[2,0,3,1],[2,3,1,0],[1,3,0,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,0,1],[2,0,3,1],[2,3,1,0],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [670, 1238, 1278, 1288] [47, 99, 151, 203, 255, 413, 416, 417, 419, 420, 426, 427, 429, 436, 437, 440, 466, 467, 473, 476, 477, 501, 503, 504, 511, 677, 1112, 1241, 1248, 1251, 1315, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4283, 4343, 4398, 4405, 4435, 4442, 4470, 4482, 4608, 4635] :=
    ⟨Fin 4, «All4x4Tables [[3,2,0,1],[2,0,3,1],[2,3,1,0],[1,3,0,2]]», Finite.of_fintype _, by decideFin!⟩
