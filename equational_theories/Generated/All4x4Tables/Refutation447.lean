
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [53, 66, 170, 177, 273, 281, 1117, 1152, 1155, 2538, 2573, 2576, 4273, 4369] [99, 203, 411, 614, 817, 1022, 1025, 1026, 1028, 1035, 1039, 1045, 1082, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2443, 2446, 2447, 2449, 2456, 2466, 2470, 2506, 2507, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4270, 4275, 4283, 4320, 4380, 4585, 4590, 4635] :=
    ⟨Fin 4, «FinitePoly [[1,2,0,3],[3,0,2,1],[2,1,3,0],[0,3,1,2]]», by decideFin!⟩
