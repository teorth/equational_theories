
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 3, 3], [3, 2, 0, 3], [0, 3, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 3, 3], [3, 2, 0, 3], [0, 3, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 3, 3], [3, 2, 0, 3], [0, 3, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 3, 3], [3, 2, 0, 3], [0, 3, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2449, 2469, 2543, 2736] [3, 8, 23, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2443, 2444, 2456, 2457, 2459, 2494, 2496, 2530, 2534, 2645, 2646, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2662, 2663, 2669, 2670, 2672, 2673, 2696, 2697, 2699, 2700, 2706, 2707, 2709, 2710, 2733, 2734, 2737, 2743, 2744, 2746, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4273, 4290, 4380, 4588, 4605] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 3, 3], [3, 2, 0, 3], [0, 3, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
