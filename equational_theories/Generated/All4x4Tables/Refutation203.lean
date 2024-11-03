
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,1],[0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,1],[0,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,1],[0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,1],[0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2296, 2351, 2402, 2554] [221, 2256, 2300, 2443, 2456, 2469, 2506, 3749, 4320] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,1],[0,2,0]]», Finite.of_fintype _, by decideFin!⟩
