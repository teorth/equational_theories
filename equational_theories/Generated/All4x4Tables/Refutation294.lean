
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 3, 1], [2, 2, 3, 3], [2, 2, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 3, 1], [2, 2, 3, 3], [2, 2, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 3, 1], [2, 2, 3, 3], [2, 2, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 3, 1], [2, 2, 3, 3], [2, 2, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [231, 2588, 2812, 4276] [23, 211, 1629, 2238, 2449, 2466, 2496, 2530, 2533, 2652, 2662, 2706, 2733, 3050, 3456, 3659, 4090, 4118, 4128, 4165, 4590] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 3, 1], [2, 2, 3, 3], [2, 2, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
