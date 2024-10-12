
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2944] [817, 1023, 1026, 1028, 1049, 1086, 1109, 1229, 1239, 1248, 1252, 1278, 1429, 1451, 1488, 1515, 1637, 1645, 1682, 1722, 1857, 1885, 1887, 1925, 2038, 2041, 2043, 2124, 2246, 2254, 2293, 2300, 2340, 2444, 2466, 2503, 2530, 2541, 2543, 2644, 2855, 2865, 2872, 2900, 2949, 3056, 3068, 3105, 3143, 3152, 3256, 3271, 3315, 3346, 3464, 3474, 3481, 3509, 3558, 3659, 3865, 3868, 3870, 3928, 3951, 4071, 4090, 4120, 4165, 4270, 4290, 4320, 4396, 4433, 4473, 4480, 4590, 4598, 4605] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]», by decideFin!⟩
