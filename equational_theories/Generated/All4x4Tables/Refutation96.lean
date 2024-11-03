
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,1],[1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,1],[1,0,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,1],[1,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,1],[1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2517] [203, 2256, 2263, 2266, 2293, 2300, 2303, 2330, 2449, 2533, 2709, 3065, 3115, 3519, 3749, 4070, 4128, 4320] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,1],[1,0,0]]», Finite.of_fintype _, by decideFin!⟩
