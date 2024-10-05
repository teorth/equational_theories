
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,6,0],[4,5,6,0,1,2,3],[0,1,2,3,4,5,6],[3,4,5,6,0,1,2],[6,0,1,2,3,4,5],[2,3,4,5,6,0,1],[5,6,0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,6,0],[4,5,6,0,1,2,3],[0,1,2,3,4,5,6],[3,4,5,6,0,1,2],[6,0,1,2,3,4,5],[2,3,4,5,6,0,1],[5,6,0,1,2,3,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,4,5,6,0],[4,5,6,0,1,2,3],[0,1,2,3,4,5,6],[3,4,5,6,0,1,2],[6,0,1,2,3,4,5],[2,3,4,5,6,0,1],[5,6,0,1,2,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,6,0],[4,5,6,0,1,2,3],[0,1,2,3,4,5,6],[3,4,5,6,0,1,2],[6,0,1,2,3,4,5],[2,3,4,5,6,0,1],[5,6,0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1279, 2044] [47, 99, 151, 255, 411, 614, 817, 1020, 1229, 1242, 1426, 1629, 1832, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4380] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,4,5,6,0],[4,5,6,0,1,2,3],[0,1,2,3,4,5,6],[3,4,5,6,0,1,2],[6,0,1,2,3,4,5],[2,3,4,5,6,0,1],[5,6,0,1,2,3,4]]», by decideFin!⟩
