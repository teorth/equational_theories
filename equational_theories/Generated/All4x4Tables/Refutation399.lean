
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1029] [411, 614, 1036, 1038, 1045, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2847, 3050, 3253, 3456, 3862, 4073, 4118, 4127, 4283, 4398, 4435, 4470, 4656] :=
    ⟨Fin 4, «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]», Finite.of_fintype _, by decideFin!⟩
