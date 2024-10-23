
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,1],[1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,1],[1,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,1],[1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,1],[1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2588, 2812] [211, 221, 2238, 2449, 2466, 2496, 2533, 2709, 3115, 3152, 3659, 4070, 4090, 4118, 4128, 4155, 4320, 4606] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,1],[1,0,1]]», Finite.of_fintype _, by decideFin!⟩
