
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 3, 1, 1], [2, 0, 3, 2], [1, 0, 3, 1], [2, 0, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 3, 1, 1], [2, 0, 3, 2], [1, 0, 3, 1], [2, 0, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 3, 1, 1], [2, 0, 3, 2], [1, 0, 3, 1], [2, 0, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 3, 1, 1], [2, 0, 3, 2], [1, 0, 3, 1], [2, 0, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1681] [8, 99, 151, 359, 411, 1020, 1223, 1832, 2035, 3253, 3887, 3915, 4065] :=
    ⟨Fin 4, «FinitePoly [[2, 3, 1, 1], [2, 0, 3, 2], [1, 0, 3, 1], [2, 0, 0, 1]]», by decideFin!⟩
