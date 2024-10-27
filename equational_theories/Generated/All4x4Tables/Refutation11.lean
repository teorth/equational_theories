
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[4,1,6,5,3,2,0],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3],[0,6,4,2,1,3,5],[5,4,0,3,6,1,2],[3,5,2,6,0,4,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0,6],[4,1,6,5,3,2,0],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3],[0,6,4,2,1,3,5],[5,4,0,3,6,1,2],[3,5,2,6,0,4,1]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0,6],[4,1,6,5,3,2,0],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3],[0,6,4,2,1,3,5],[5,4,0,3,6,1,2],[3,5,2,6,0,4,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0,6],[4,1,6,5,3,2,0],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3],[0,6,4,2,1,3,5],[5,4,0,3,6,1,2],[3,5,2,6,0,4,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [677] [47, 99, 151, 203, 261, 274, 283, 411, 670, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3722, 3749, 3862, 4065, 4283, 4343, 4380, 4608, 4635] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,4,5,0,6],[4,1,6,5,3,2,0],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3],[0,6,4,2,1,3,5],[5,4,0,3,6,1,2],[3,5,2,6,0,4,1]]», Finite.of_fintype _, by decideFin!⟩
