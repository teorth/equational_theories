
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,5,6,1],[6,1,0,5,2,4,3],[1,4,2,0,6,3,5],[2,6,5,3,0,1,4],[3,5,1,6,4,0,2],[4,3,6,2,1,5,0],[5,0,4,1,3,2,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,2,4,3],[1,4,2,0,6,3,5],[2,6,5,3,0,1,4],[3,5,1,6,4,0,2],[4,3,6,2,1,5,0],[5,0,4,1,3,2,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,3,4,5,6,1],[6,1,0,5,2,4,3],[1,4,2,0,6,3,5],[2,6,5,3,0,1,4],[3,5,1,6,4,0,2],[4,3,6,2,1,5,0],[5,0,4,1,3,2,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,2,4,3],[1,4,2,0,6,3,5],[2,6,5,3,0,1,4],[3,5,1,6,4,0,2],[4,3,6,2,1,5,0],[5,0,4,1,3,2,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1119, 2856] [117, 258, 261, 263, 429, 473, 513, 1085, 1231, 1278, 1654, 1721, 1850, 1897, 2036, 2044, 2053, 2054, 2060, 2061, 2100, 2646, 2653, 2660, 2663, 2672, 2850, 2852, 2873, 2875, 3254, 3255, 3256, 3271, 3318, 3343, 3457, 3458, 3459, 3518, 4073, 4131, 4268, 4598, 4656] :=
    ⟨Fin 7, «FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,2,4,3],[1,4,2,0,6,3,5],[2,6,5,3,0,1,4],[3,5,1,6,4,0,2],[4,3,6,2,1,5,0],[5,0,4,1,3,2,6]]», by decideFin!⟩
