
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,2],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,2],[0,0,2],[0,0,1]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,0,2],[0,0,1]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,2],[0,0,2],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2310, 2318, 2351, 2364, 2385, 2530, 2706, 2812, 3458] [2293, 2496, 2543, 2646, 2652, 2662, 2709, 3058, 3065, 3152, 3253, 3459, 3461, 3525, 3537, 3659, 4070, 4090, 4314, 4320, 4622, 4631] :=
    ⟨Fin 3, «All4x4Tables [[0,1,2],[0,0,2],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
