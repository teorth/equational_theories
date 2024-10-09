
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,1],[2,2,1,1],[2,2,2,2],[2,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,1],[2,2,1,1],[2,2,2,2],[2,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,1],[2,2,1,1],[2,2,2,2],[2,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,1],[2,2,1,1],[2,2,2,2],[2,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [840, 1260] [818, 3660, 3721] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,1],[2,2,1,1],[2,2,2,2],[2,3,3,2]]», by decideFin!⟩
