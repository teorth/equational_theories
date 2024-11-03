
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3197] [203, 1629, 2238, 2441, 2652, 2709, 3058, 3519, 3522, 3659, 4065, 4622] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,1],[2,3,2,3],[3,1,3,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
