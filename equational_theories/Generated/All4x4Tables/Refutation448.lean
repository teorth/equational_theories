
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 2, 3], [3, 3, 2, 0], [2, 2, 2, 0], [3, 0, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 2, 3], [3, 3, 2, 0], [2, 2, 2, 0], [3, 0, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 2, 3], [3, 3, 2, 0], [2, 2, 2, 0], [3, 0, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 2, 3], [3, 3, 2, 0], [2, 2, 2, 0], [3, 0, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3548] [3316, 3318, 3343, 3345, 4065, 4398, 4405, 4435, 4442] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 2, 3], [3, 3, 2, 0], [2, 2, 2, 0], [3, 0, 0, 3]]», by decideFin!⟩
