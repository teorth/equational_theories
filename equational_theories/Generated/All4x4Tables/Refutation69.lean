
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2743, 2847] [23, 39, 99, 411, 1721, 1897, 2035, 2699, 2909, 2939, 3068, 4283, 4598] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,0,2,1],[2,1,3,0],[0,2,3,1]]», Finite.of_fintype _, by decideFin!⟩
