
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [273, 280] [1020, 1629, 1840, 1921, 3319, 3353, 3915, 3962, 4275] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]», Finite.of_fintype _, by decideFin!⟩
