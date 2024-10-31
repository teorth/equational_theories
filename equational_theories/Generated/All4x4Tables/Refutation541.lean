
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,1,1],[3,3,0,0],[2,2,0,0],[3,3,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,1,1],[3,3,0,0],[2,2,0,0],[3,3,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,1,1],[3,3,0,0],[2,2,0,0],[3,3,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,1,1],[3,3,0,0],[2,2,0,0],[3,3,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [162] [4070, 4118, 4584] :=
    ⟨Fin 4, «FinitePoly [[2,2,1,1],[3,3,0,0],[2,2,0,0],[3,3,1,1]]», Finite.of_fintype _, by decideFin!⟩
