
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 1], [3, 1, 1, 3], [1, 1, 2, 2], [2, 3, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 1], [3, 1, 1, 3], [1, 1, 2, 2], [2, 3, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 1], [3, 1, 1, 3], [1, 1, 2, 2], [2, 3, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 1], [3, 1, 1, 3], [1, 1, 2, 2], [2, 3, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3722, 3961, 4293] [43, 307, 359, 3253, 3512, 3518, 3519, 3548, 3549, 3555, 3918, 3925, 3954, 3955, 4065, 4283, 4380, 4635] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 1], [3, 1, 1, 3], [1, 1, 2, 2], [2, 3, 2, 3]]», by decideFin!⟩
