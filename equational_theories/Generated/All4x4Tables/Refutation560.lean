
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,2,1],[3,0,1,2],[2,1,0,3],[1,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,2,1],[3,0,1,2],[2,1,0,3],[1,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,2,1],[3,0,1,2],[2,1,0,3],[1,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,2,1],[3,0,1,2],[2,1,0,3],[1,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [775, 1710] [99, 417, 419, 436, 440, 466, 504, 620, 630, 643, 669, 676, 817, 1036, 1038, 1045, 1049, 1075, 1082, 1086, 1241, 1252, 1276, 1285, 1434, 1479, 1632, 1635, 1654, 1684, 1691, 1722, 1838, 1840, 1848, 1894, 1921, 1925, 2060, 2088, 2244, 2256, 2291, 2340, 2447, 2449, 2457, 2459, 2496, 2541, 2543, 2644, 2853, 2863, 2902, 2909, 2949, 3058, 3066, 3075, 3112, 3143, 3152, 3253, 3456, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3862, 4065, 4273, 4275, 4290, 4320, 4396, 4433, 4473, 4480, 4585, 4588, 4598, 4605] :=
    ⟨Fin 4, «FinitePoly [[0,3,2,1],[3,0,1,2],[2,1,0,3],[1,2,3,0]]», Finite.of_fintype _, by decideFin!⟩
