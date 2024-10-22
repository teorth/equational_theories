
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[1,2,0,1],[3,2,0,2],[3,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[1,2,0,1],[3,2,0,2],[3,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[1,2,0,1],[3,2,0,2],[3,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[1,2,0,1],[3,2,0,2],[3,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [838] [4316] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[1,2,0,1],[3,2,0,2],[3,2,3,1]]», Finite.of_fintype _, by decideFin!⟩
