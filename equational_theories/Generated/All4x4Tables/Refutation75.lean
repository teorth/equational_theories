
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,3,2,3],[2,1,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,3,2,3],[2,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,3,2,3],[2,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,3,2,3],[2,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [316, 2506, 2554, 3488] [212, 221, 1426, 1630, 1631, 1632, 1634, 1635, 1638, 1644, 1645, 1648, 1654, 1655, 1657, 1721, 1832, 2240, 2243, 2244, 2247, 2254, 2256, 2257, 2264, 2293, 2300, 2330, 2443, 2444, 2447, 2449, 2456, 2457, 2459, 2460, 2467, 2469, 2470, 2517, 2646, 2699, 2736, 3052, 3055, 3056, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3105, 3115, 3142, 3254, 3255, 3259, 3261, 3269, 3271, 3279, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3457, 3459, 3461, 3462, 3465, 3475, 3481, 3511, 3512, 3518, 3519, 3521, 3786, 4066, 4067, 4070, 4071, 4073, 4074, 4084, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4268, 4269, 4273, 4283, 4284, 4314, 4320, 4583, 4584, 4585, 4599, 4606, 4629, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,3,2,3],[2,1,3,3],[0,1,2,3]]», by decideFin!⟩
