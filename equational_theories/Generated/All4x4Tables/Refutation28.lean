
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[1,0,0,1],[1,0,3,2],[3,1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[1,0,0,1],[1,0,3,2],[3,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[1,0,0,1],[1,0,3,2],[3,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[1,0,0,1],[1,0,3,2],[3,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2503, 2543, 2808, 3068, 3152] [203, 307, 419, 429, 436, 466, 473, 513, 614, 817, 1028, 1038, 1045, 1075, 1082, 1109, 1122, 1223, 1426, 1629, 1840, 1857, 1887, 1894, 1921, 2035, 2238, 2443, 2449, 2459, 2466, 2469, 2496, 2506, 2530, 2533, 2646, 2647, 2650, 2652, 2659, 2660, 2662, 2672, 2709, 2736, 2847, 3052, 3058, 3065, 3075, 3105, 3112, 3115, 3255, 3256, 3258, 3259, 3261, 3268, 3271, 3278, 3308, 3315, 3456, 3659, 4065, 4269, 4270, 4272, 4283, 4320, 4321, 4343, 4380, 4584, 4585, 4590, 4598, 4606, 4658] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[1,0,0,1],[1,0,3,2],[3,1,1,0]]», by decideFin!⟩
