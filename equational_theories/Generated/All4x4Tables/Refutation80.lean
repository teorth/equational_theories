
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,2,1],[1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[2,2,1],[1,2,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[2,2,1],[1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[2,2,1],[1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2056, 2070] [2043, 2097, 2644, 2847, 3255, 3271, 3278, 3309, 3326, 3334, 3346, 3353, 3456, 3887, 3955, 3962, 4090, 4165, 4269, 4275, 4284, 4320] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[2,2,1],[1,2,1]]», Finite.of_fintype _, by decideFin!⟩
