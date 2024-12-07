
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,0,0],[2,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,0,0],[2,1,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,0,0],[2,1,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,0,0],[2,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [837, 1051] [411, 819, 832, 833, 842, 843, 1028, 1035, 1038, 1229, 1832, 3255, 3278, 3306, 3316, 3659, 3862, 4065, 4269, 4606, 4622, 4631] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,0,0],[2,1,1]]», Finite.of_fintype _, by decideFin!⟩
