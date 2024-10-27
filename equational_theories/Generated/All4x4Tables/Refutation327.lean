
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1050] [99, 151, 1036, 1038, 1045, 1223, 4380] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]», Finite.of_fintype _, by decideFin!⟩
