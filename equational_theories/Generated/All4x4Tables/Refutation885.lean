
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4164] [3308, 3352] :=
    ⟨Fin 6, «FinitePoly [[3,3,3,0,0,3],[2,5,5,5,2,2],[3,5,4,0,2,1],[0,5,0,0,0,1],[0,2,2,0,2,2],[2,2,1,1,2,1]]», Finite.of_fintype _, by decideFin!⟩
