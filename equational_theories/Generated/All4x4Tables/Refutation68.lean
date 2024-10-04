
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [827, 1236] [377, 822, 829, 1025, 1026, 1028, 1225, 1229, 1231, 1454, 1455, 1631, 1654, 1658, 1850, 2044, 2054, 2060, 2061, 2264, 2267, 2446, 2457, 2470, 2653, 2660, 2663, 2672, 2850, 2856, 2873, 2875, 3053, 3056, 3058, 3066, 3068, 3075, 3079, 3458, 3518, 3668, 3721, 3871, 3927, 4073, 4120, 4135, 4399, 4472, 4598, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]», by decideFin!⟩
