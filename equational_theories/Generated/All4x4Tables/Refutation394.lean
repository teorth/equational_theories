
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3583, 3587] [3519, 3556, 3925, 3962, 4155, 4158, 4165, 4406, 4435, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]», Finite.of_fintype _, by decideFin!⟩
