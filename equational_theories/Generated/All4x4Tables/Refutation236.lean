
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,0],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[2,2,0],[0,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[2,2,0],[0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[2,2,0],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2266, 2443, 2446] [203, 307, 1631, 2240, 2246, 2256, 2449, 2469, 2644, 3519, 3659, 4128] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[2,2,0],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
