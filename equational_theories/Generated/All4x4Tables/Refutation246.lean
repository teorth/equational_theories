
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 3, 1], [2, 1, 1, 2], [2, 2, 1, 2], [2, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 3, 1], [2, 1, 1, 2], [2, 2, 1, 2], [2, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 3, 1], [2, 1, 1, 2], [2, 2, 1, 2], [2, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 3, 1], [2, 1, 1, 2], [2, 2, 1, 2], [2, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [443, 835, 846, 3870, 3928] [8, 99, 414, 419, 429, 436, 466, 500, 504, 513, 818, 819, 820, 823, 842, 843, 845, 1020, 1223, 1832, 3253, 3659, 3915, 4270] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 3, 1], [2, 1, 1, 2], [2, 2, 1, 2], [2, 3, 3, 1]]», by decideFin!⟩
