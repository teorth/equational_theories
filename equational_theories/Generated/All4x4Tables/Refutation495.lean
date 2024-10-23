
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4,5,6],[2,3,1,4,5,6,0],[4,6,5,0,2,1,3],[5,0,6,2,1,3,4],[1,4,3,5,6,0,2],[6,2,0,1,3,4,5],[3,5,4,6,0,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4,5,6],[2,3,1,4,5,6,0],[4,6,5,0,2,1,3],[5,0,6,2,1,3,4],[1,4,3,5,6,0,2],[6,2,0,1,3,4,5],[3,5,4,6,0,2,1]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,1,2,3,4,5,6],[2,3,1,4,5,6,0],[4,6,5,0,2,1,3],[5,0,6,2,1,3,4],[1,4,3,5,6,0,2],[6,2,0,1,3,4,5],[3,5,4,6,0,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4,5,6],[2,3,1,4,5,6,0],[4,6,5,0,2,1,3],[5,0,6,2,1,3,4],[1,4,3,5,6,0,2],[6,2,0,1,3,4,5],[3,5,4,6,0,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [677, 907, 1489, 1516] [47, 99, 151, 203, 261, 411, 620, 630, 632, 633, 639, 642, 667, 669, 676, 679, 680, 707, 826, 845, 870, 872, 873, 879, 882, 906, 1020, 1223, 1434, 1454, 1479, 1519, 1525, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4273, 4275, 4283, 4343, 4380, 4585, 4588, 4608, 4635, 4636] :=
    ⟨Fin 7, «FinitePoly [[0,1,2,3,4,5,6],[2,3,1,4,5,6,0],[4,6,5,0,2,1,3],[5,0,6,2,1,3,4],[1,4,3,5,6,0,2],[6,2,0,1,3,4,5],[3,5,4,6,0,2,1]]», Finite.of_fintype _, by decideFin!⟩
