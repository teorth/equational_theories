
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,1],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,1],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,1],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,1],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [643, 846, 2543, 2746] [43, 99, 359, 411, 620, 622, 630, 632, 639, 667, 669, 676, 680, 707, 819, 825, 832, 833, 835, 836, 842, 843, 845, 870, 872, 879, 883, 906, 917, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2444, 2449, 2457, 2459, 2466, 2496, 2530, 2534, 2541, 2647, 2650, 2652, 2660, 2662, 2669, 2697, 2699, 2710, 2744, 2847, 3050, 3253, 3456, 3659, 3862, 4066, 4067, 4071, 4090, 4120, 4165, 4270, 4290, 4293, 4320, 4396, 4433, 4473, 4480, 4583, 4590, 4598, 4605, 4608, 4636] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,1],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
