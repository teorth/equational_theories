
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 2, 3], [2, 3, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 2, 3], [2, 3, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 2, 3], [2, 3, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 2, 3], [2, 3, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [224, 2376, 3509, 3769, 3786] [2530, 3461, 3464, 3694, 3820] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 2, 3], [2, 3, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]]», by decideFin!⟩
