
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[5,4,0,3,6,1,2],[4,1,6,5,3,2,0],[0,6,4,2,1,3,5],[3,5,2,6,0,4,1],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0,6],[5,4,0,3,6,1,2],[4,1,6,5,3,2,0],[0,6,4,2,1,3,5],[3,5,2,6,0,4,1],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0,6],[5,4,0,3,6,1,2],[4,1,6,5,3,2,0],[0,6,4,2,1,3,5],[3,5,2,6,0,4,1],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0,6],[5,4,0,3,6,1,2],[4,1,6,5,3,2,0],[0,6,4,2,1,3,5],[3,5,2,6,0,4,1],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2328] [47, 151, 203, 255, 411, 614, 817, 1020, 1223, 1482, 1629, 1832, 2035, 2300, 2330, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4290, 4380, 4656] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,4,5,0,6],[5,4,0,3,6,1,2],[4,1,6,5,3,2,0],[0,6,4,2,1,3,5],[3,5,2,6,0,4,1],[6,3,1,0,2,5,4],[2,0,5,1,4,6,3]]», Finite.of_fintype _, by decideFin!⟩
