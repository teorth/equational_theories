
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [826, 3113] [47, 99, 151, 203, 255, 359, 614, 1020, 1223, 1426, 2035, 2238, 2644, 2847, 3253, 3659, 3862, 4380] :=
    ⟨Fin 5, «FinitePoly [[1,2,3,0,4],[0,3,1,4,2],[2,0,4,3,1],[4,1,0,2,3],[3,4,2,1,0]]», Finite.of_fintype _, by decideFin!⟩
