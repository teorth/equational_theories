
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,2],[2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,2],[2,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,2],[2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,2],[2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [658, 676, 1082, 1481, 1523, 1543, 1850, 1929, 2132, 2402, 2964, 4424] [617, 632, 639, 669, 825, 870, 879, 917, 1038, 1113, 1229, 1289, 1444, 1451, 1479, 1488, 1635, 1645, 1654, 1658, 1682, 1684, 1848, 1885, 1894, 2088, 2254, 2267, 2291, 2338, 2444, 2447, 2449, 2534, 2541, 2669, 2697, 2900, 2940, 2947, 2998, 3103, 3116, 3150, 3201, 3271, 3342, 3474, 3481, 3545, 3556, 3558, 3588, 3667, 3675, 3714, 3748, 3752, 3761, 3880, 3924, 3951, 3964, 3994, 4073, 4081, 4083, 4158, 4167, 4273, 4320, 4369, 4405, 4435, 4473, 4480, 4531, 4598, 4605, 4635, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,2],[2,1,0]]», Finite.of_fintype _, by decideFin!⟩
