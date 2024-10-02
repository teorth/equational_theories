
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 2, 3], [3, 2, 0, 3], [3, 0, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 2, 3], [3, 2, 0, 3], [3, 0, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 2, 3], [3, 2, 0, 3], [3, 0, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 2, 3], [3, 2, 0, 3], [3, 0, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2256, 2266, 2330, 2506] [23, 203, 1629, 2246, 2253, 2263, 2290, 2293, 2300, 2303, 2327, 2449, 2456, 2466, 2496, 2530, 2533, 2645, 2646, 2647, 2649, 2650, 2652, 2653, 2659, 2660, 2663, 2669, 2670, 2672, 2673, 2696, 2697, 2699, 2700, 2706, 2707, 2709, 2710, 2733, 2734, 2736, 2737, 2743, 2744, 3050, 3456, 3659, 4090, 4118, 4128, 4165, 4590] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 2, 3], [3, 2, 0, 3], [3, 0, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
