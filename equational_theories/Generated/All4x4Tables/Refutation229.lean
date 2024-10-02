
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3056, 3068, 3319] [151, 1426, 1629, 2441, 2644, 3055, 3065, 3075, 3079, 3102, 3112, 3139, 3149, 3261, 3262, 3306, 3456, 4314] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]», by decideFin!⟩
