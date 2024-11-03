
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,1],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,1],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,1],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,1],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2385, 2484, 2588, 2778, 2812] [1629, 2300, 2443, 2459, 2466, 2496, 2530, 2533, 2646, 2652, 2659, 2699, 2709, 3050, 3253, 3456, 3659, 4068, 4070, 4090, 4128, 4131, 4165, 4269, 4270, 4272, 4314, 4622, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,1],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
