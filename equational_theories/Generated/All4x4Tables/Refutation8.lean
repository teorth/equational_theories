
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1],[0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1],[0,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[1,1],[0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1],[0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [24] [47, 99, 255, 359, 411, 614, 817, 1020, 1223, 2035, 2644, 2847, 3659, 3862, 4083, 4091, 4165, 4293, 4320, 4380, 4587, 4588, 4605, 4606, 4608, 4635, 4636] :=
    ⟨Fin 2, «FinitePoly [[1,1],[0,0]]», Finite.of_fintype _, by decideFin!⟩
