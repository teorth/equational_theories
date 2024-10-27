
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [104, 1254, 1262] [1020, 1244, 1832, 4591] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,2,0,1],[2,3,2,2],[2,3,3,2]]», Finite.of_fintype _, by decideFin!⟩
