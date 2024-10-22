
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [50, 125, 211, 222, 280] [151, 231, 283, 614, 1832, 2441, 3253, 3862, 4276, 4290, 4320, 4396, 4433, 4473, 4480, 4591, 4598, 4605] :=
    ⟨Fin 4, «FinitePoly [[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]]», Finite.of_fintype _, by decideFin!⟩
