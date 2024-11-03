
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,2,2],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[2,2,2],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[2,2,2],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[2,2,2],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1430, 3513, 3523, 4357] [1629, 1832, 2035, 3253, 3458, 3459, 3461, 3462, 3464, 3465, 3509, 3518, 3519, 3659, 3862, 4065, 4269, 4270, 4283, 4284, 4380, 4583, 4585, 4598, 4599, 4629] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[2,2,2],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
