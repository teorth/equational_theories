
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 0, 1], [2, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 0, 1], [2, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 0, 1], [2, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 0, 1], [2, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [106, 1023, 1247, 3662, 3726, 3727, 3864, 3870, 4598] [375, 377, 414, 823, 842, 1036, 3663, 3729, 3873, 3928, 4118, 4120, 4121, 4127, 4128, 4130, 4673] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 0, 1], [2, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 1]]», by decideFin!⟩
