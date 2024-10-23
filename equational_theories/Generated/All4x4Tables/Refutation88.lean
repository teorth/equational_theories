
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,1],[1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[2,2,1],[1,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[2,2,1],[1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[2,2,1],[1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1655, 3261] [1832, 2238, 2441, 3050, 3254, 3255, 3256, 3259, 3308, 3315, 3316, 3318, 3319, 3456, 4065, 4268, 4283, 4314, 4585] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[2,2,1],[1,0,1]]», Finite.of_fintype _, by decideFin!⟩
