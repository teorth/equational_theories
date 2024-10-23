
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,6,2,0,5,3,4],[2,4,5,3,0,6,1],[0,2,3,4,6,1,5],[5,1,0,6,3,4,2],[4,3,1,5,2,0,6],[6,0,4,2,1,5,3],[3,5,6,1,4,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,6,2,0,5,3,4],[2,4,5,3,0,6,1],[0,2,3,4,6,1,5],[5,1,0,6,3,4,2],[4,3,1,5,2,0,6],[6,0,4,2,1,5,3],[3,5,6,1,4,2,0]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,6,2,0,5,3,4],[2,4,5,3,0,6,1],[0,2,3,4,6,1,5],[5,1,0,6,3,4,2],[4,3,1,5,2,0,6],[6,0,4,2,1,5,3],[3,5,6,1,4,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,6,2,0,5,3,4],[2,4,5,3,0,6,1],[0,2,3,4,6,1,5],[5,1,0,6,3,4,2],[4,3,1,5,2,0,6],[6,0,4,2,1,5,3],[3,5,6,1,4,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2467] [151, 203, 1426, 1629, 1832, 2238, 2443, 2449, 2457, 2460, 3050, 3253, 3456, 4065, 4268, 4314, 4585, 4598] :=
    ⟨Fin 7, «FinitePoly [[1,6,2,0,5,3,4],[2,4,5,3,0,6,1],[0,2,3,4,6,1,5],[5,1,0,6,3,4,2],[4,3,1,5,2,0,6],[6,0,4,2,1,5,3],[3,5,6,1,4,2,0]]», Finite.of_fintype _, by decideFin!⟩
