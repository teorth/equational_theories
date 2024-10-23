
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[1,0,3,2],[3,2,1,0],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[1,0,3,2],[3,2,1,0],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[1,0,3,2],[3,2,1,0],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[1,0,3,2],[3,2,1,0],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2592, 2722, 2808] [417, 427, 440, 477, 504, 511, 614, 820, 823, 825, 833, 835, 842, 846, 870, 872, 879, 883, 906, 917, 1023, 1028, 1038, 1049, 1082, 1109, 1223, 1426, 1632, 1637, 1645, 1654, 1684, 1838, 1857, 1887, 1894, 1925, 2035, 2238, 2444, 2449, 2457, 2466, 2496, 2530, 2541, 2647, 2652, 2662, 2697, 2744, 2847, 3058, 3066, 3075, 3105, 3116, 3150, 3256, 3259, 3308, 3315, 3342, 3456, 3659, 3865, 3870, 3880, 3917, 3928, 3955, 3964, 4065, 4270, 4273, 4283, 4290, 4380, 4585, 4590, 4598, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[1,0,3,2],[3,2,1,0],[2,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
