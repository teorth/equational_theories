
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,0,1],[3,0,1,2],[0,1,2,3],[1,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,0,1],[3,0,1,2],[0,1,2,3],[1,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,0,1],[3,0,1,2],[0,1,2,3],[1,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,0,1],[3,0,1,2],[0,1,2,3],[1,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [440, 513, 714, 883, 910, 917, 1323, 1492, 1528, 1729, 1898, 1932, 2064, 2304, 2331, 2507, 2710, 2737, 2744, 3079, 3152] [417, 419, 427, 429, 436, 466, 473, 620, 622, 630, 632, 639, 669, 676, 825, 833, 835, 842, 870, 872, 879, 906, 1023, 1026, 1028, 1036, 1038, 1045, 1075, 1082, 1109, 1229, 1239, 1241, 1276, 1434, 1451, 1479, 1488, 1515, 1632, 1635, 1637, 1645, 1654, 1682, 1684, 1691, 1838, 1840, 1848, 1857, 1885, 1887, 1894, 1921, 2038, 2041, 2043, 2060, 2088, 2244, 2256, 2291, 2293, 2300, 2444, 2447, 2449, 2457, 2459, 2466, 2496, 2503, 2530, 2647, 2650, 2652, 2660, 2662, 2669, 2697, 2699, 2853, 2855, 2863, 2865, 2872, 2900, 2902, 2909, 3056, 3058, 3066, 3068, 3075, 3105, 3112, 3253, 3456, 3659, 3862, 4065, 4270, 4273, 4275, 4585, 4588, 4590] :=
    ⟨Fin 4, «FinitePoly [[2,3,0,1],[3,0,1,2],[0,1,2,3],[1,2,3,0]]», Finite.of_fintype _, by decideFin!⟩
