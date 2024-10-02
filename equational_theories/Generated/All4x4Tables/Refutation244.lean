
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [323, 2533, 2709, 4362] [23, 309, 310, 312, 313, 316, 326, 333, 1629, 2444, 2456, 2457, 2459, 2494, 2496, 2530, 2534, 2652, 2659, 2672, 2696, 2706, 2733, 2746, 3050, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3319, 3346, 3353, 3456, 4065, 4276, 4321, 4343] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 3], [3, 3, 3, 3], [1, 1, 1, 3], [0, 1, 2, 3]]», by decideFin!⟩
