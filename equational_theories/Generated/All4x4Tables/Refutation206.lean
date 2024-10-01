
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 2, 1], [3, 1, 2, 3], [3, 1, 2, 3], [0, 1, 1, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 2, 1], [3, 1, 2, 3], [3, 1, 2, 3], [0, 1, 1, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 2, 1], [3, 1, 2, 3], [3, 1, 2, 3], [0, 1, 1, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 2, 1], [3, 1, 2, 3], [3, 1, 2, 3], [0, 1, 1, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [260, 2919, 3712, 4320] [270, 280, 2936, 2946, 3253, 3522, 3759, 4065, 4362] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 2, 1], [3, 1, 2, 3], [3, 1, 2, 3], [0, 1, 1, 3]]», by decideFin!⟩
