
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [319, 2623] [2263, 2293, 2449, 3261, 3269, 3459, 3481, 3519, 3749, 4362, 4606, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
