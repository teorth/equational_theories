
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,0,1],[2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[1,0,1],[2,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[1,0,1],[2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[1,0,1],[2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [368, 1257] [1025, 1039, 1228, 1242, 4070, 4084] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[1,0,1],[2,1,0]]», Finite.of_fintype _, by decideFin!⟩
