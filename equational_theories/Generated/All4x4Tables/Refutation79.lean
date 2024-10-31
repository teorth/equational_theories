
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[2,0,2],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[2,0,2],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[2,0,2],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[2,0,2],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1432] [1635, 4131] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[2,0,2],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
