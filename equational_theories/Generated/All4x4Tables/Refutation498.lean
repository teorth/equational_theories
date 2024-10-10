
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1285, 1313] [99, 151, 203, 255, 359, 411, 614, 817, 1229, 1242, 1278, 1279, 1426, 1629, 1832, 2238, 2441, 2644, 2847, 3050, 3253, 3456] :=
    ⟨Fin 7, «FinitePoly [[1,2,0,3,6,4,5],[3,1,6,5,2,0,4],[4,5,1,0,3,2,6],[2,6,4,1,0,5,3],[5,3,2,4,1,6,0],[0,4,3,6,5,1,2],[6,0,5,2,4,3,1]]», by decideFin!⟩
