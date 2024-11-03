
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,0,3,0],[3,0,3,0],[3,3,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,0,3,0],[3,0,3,0],[3,3,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,0,3,0],[3,0,3,0],[3,3,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,0,3,0],[3,0,3,0],[3,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3481] [3659, 4065] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,0,3,0],[3,0,3,0],[3,3,0,0]]», Finite.of_fintype _, by decideFin!⟩
