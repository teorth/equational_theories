
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [443] [99, 426, 429, 436, 819, 832, 833, 836, 842, 843, 845, 1020, 1223, 1832, 3253, 3659, 3864, 3865, 3867, 3878, 3881, 3887, 3888, 3915, 3925, 4065, 4269, 4270, 4293, 4314, 4583, 4591, 4598, 4606, 4608, 4622, 4631, 4636, 4647] :=
    ⟨Fin 4, «All4x4Tables [[2,0,3,1],[2,1,1,2],[2,2,1,2],[2,3,3,1]]», Finite.of_fintype _, by decideFin!⟩
