
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[0,0,1],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[0,0,1],[1,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[0,0,1],[1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[0,0,1],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1738] [3253, 3456, 3862, 4065, 4269, 4272, 4275, 4283, 4284, 4291, 4314, 4320, 4380, 4606, 4631, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[0,0,1],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
