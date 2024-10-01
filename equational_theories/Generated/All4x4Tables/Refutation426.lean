
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2998, 3152, 3903] [26, 29, 1632, 1635, 1645, 1647, 1654, 1658, 1682, 1684, 1691, 1695, 1722, 1729, 2238, 2444, 2447, 2449, 2457, 2459, 2470, 2494, 2503, 2507, 2530, 2534, 2541, 2647, 2650, 2660, 2669, 2673, 2697, 2699, 2710, 2737, 2744, 2850, 2853, 2855, 2863, 2876, 2900, 2913, 2936, 2940, 2947, 3053, 3056, 3066, 3068, 3075, 3079, 3103, 3105, 3112, 3116, 3143, 3150, 3462, 3474, 3887, 3915, 4071, 4073, 4081, 4083] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]», by decideFin!⟩
