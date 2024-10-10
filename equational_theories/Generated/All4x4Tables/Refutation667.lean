
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,4,3,2,4],[0,4,3,0,4],[2,4,2,2,4],[2,4,2,2,4],[2,4,2,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,4,3,2,4],[0,4,3,0,4],[2,4,2,2,4],[2,4,2,2,4],[2,4,2,2,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,4,3,2,4],[0,4,3,0,4],[2,4,2,2,4],[2,4,2,2,4],[2,4,2,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,4,3,2,4],[0,4,3,0,4],[2,4,2,2,4],[2,4,2,2,4],[2,4,2,2,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3698] [3674] :=
    ⟨Fin 5, «FinitePoly [[2,4,3,2,4],[0,4,3,0,4],[2,4,2,2,4],[2,4,2,2,4],[2,4,2,2,4]]», by decideFin!⟩
