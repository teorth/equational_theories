
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1633] [151, 203, 1426, 1635, 1832, 2238, 2443, 2446, 2449, 3055, 3253, 3457, 3458, 3459, 3511, 3518, 3519, 4120, 4121, 4127, 4128, 4130, 4131, 4598, 4599, 4629] :=
    ⟨Fin 4, «All4x4Tables [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]», Finite.of_fintype _, by decideFin!⟩
