
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,0,0,3],[2,2,2,2],[0,0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,0,0,3],[2,2,2,2],[0,0,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,0,0,3],[2,2,2,2],[0,0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,0,0,3],[2,2,2,2],[0,0,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1443, 1630, 3055] [151, 203, 1428, 1429, 1431, 1432, 1434, 1435, 1444, 1445, 1451, 1452, 1454, 1455, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1832, 2238, 2442, 2443, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2459, 2460, 2466, 2467, 2469, 2470, 3051, 3052, 3053, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3253, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3509, 3512, 3518, 3519, 4066, 4068, 4070, 4071, 4073, 4074, 4120, 4121, 4127, 4128, 4130, 4269, 4270, 4283, 4284, 4314, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,0,0,3],[2,2,2,2],[0,0,0,1]]», by decideFin!⟩
