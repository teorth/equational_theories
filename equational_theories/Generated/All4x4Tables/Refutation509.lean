
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,5,6,1],[6,1,0,5,3,2,4],[1,5,2,0,6,4,3],[2,4,6,3,0,1,5],[3,6,5,1,4,0,2],[4,3,1,6,2,5,0],[5,0,4,2,1,3,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,3,2,4],[1,5,2,0,6,4,3],[2,4,6,3,0,1,5],[3,6,5,1,4,0,2],[4,3,1,6,2,5,0],[5,0,4,2,1,3,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,3,4,5,6,1],[6,1,0,5,3,2,4],[1,5,2,0,6,4,3],[2,4,6,3,0,1,5],[3,6,5,1,4,0,2],[4,3,1,6,2,5,0],[5,0,4,2,1,3,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,3,2,4],[1,5,2,0,6,4,3],[2,4,6,3,0,1,5],[3,6,5,1,4,0,2],[4,3,1,6,2,5,0],[5,0,4,2,1,3,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [713, 2450] [55, 65, 72, 209, 619, 632, 642, 679, 703, 832, 845, 872, 909, 916, 1434, 1444, 1452, 1478, 1491, 1518, 1525, 1647, 1655, 1840, 1851, 2254, 2263, 2467, 3056, 3068, 3079, 3261, 3306, 3867, 3877, 3887, 3962, 4070, 4071, 4080, 4090, 4130, 4155, 4275, 4320, 4666] :=
    ⟨Fin 7, «FinitePoly [[0,2,3,4,5,6,1],[6,1,0,5,3,2,4],[1,5,2,0,6,4,3],[2,4,6,3,0,1,5],[3,6,5,1,4,0,2],[4,3,1,6,2,5,0],[5,0,4,2,1,3,6]]», by decideFin!⟩
