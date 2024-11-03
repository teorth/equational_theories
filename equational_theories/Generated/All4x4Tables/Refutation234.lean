
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,2,1],[0,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[0,2,1],[0,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[0,2,1],[0,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[0,2,1],[0,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [166, 3993] [1832, 2090, 2127, 2134, 3253, 3456, 3864, 3870, 3880, 3887, 3890, 4065] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[0,2,1],[0,0,1]]», Finite.of_fintype _, by decideFin!⟩
