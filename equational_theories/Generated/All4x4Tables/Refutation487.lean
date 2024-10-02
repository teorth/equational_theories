
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 2, 3], [3, 3, 3, 3], [2, 0, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [2, 0, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 2, 3], [3, 3, 3, 3], [2, 0, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [2, 0, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [246, 316, 2389, 2402, 2430, 2459, 2699, 3294, 3297, 4355] [8, 26, 29, 204, 205, 206, 208, 209, 212, 219, 221, 222, 228, 229, 308, 309, 313, 315, 323, 325, 326, 333, 335, 411, 614, 817, 1020, 1223, 1426, 1632, 1635, 1645, 1647, 1654, 1658, 1682, 1684, 1691, 1695, 1722, 1729, 1832, 2035, 2241, 2244, 2254, 2267, 2291, 2304, 2331, 2338, 2444, 2446, 2447, 2457, 2470, 2494, 2503, 2507, 2533, 2534, 2541, 2647, 2650, 2660, 2669, 2673, 2697, 2710, 2737, 2744, 2847, 3053, 3056, 3066, 3075, 3079, 3103, 3105, 3112, 3116, 3143, 3150, 3306, 3319, 3353, 3458, 3471, 3482, 3862, 4275, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [2, 0, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
