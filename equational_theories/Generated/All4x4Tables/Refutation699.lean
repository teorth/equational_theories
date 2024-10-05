
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,4,5,5,0],[1,4,4,5,5,0],[2,4,4,5,5,0],[1,3,3,5,5,0],[2,4,4,5,5,0],[2,3,4,5,5,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,4,5,5,0],[1,4,4,5,5,0],[2,4,4,5,5,0],[1,3,3,5,5,0],[2,4,4,5,5,0],[2,3,4,5,5,0]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,3,4,5,5,0],[1,4,4,5,5,0],[2,4,4,5,5,0],[1,3,3,5,5,0],[2,4,4,5,5,0],[2,3,4,5,5,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,4,5,5,0],[1,4,4,5,5,0],[2,4,4,5,5,0],[1,3,3,5,5,0],[2,4,4,5,5,0],[2,3,4,5,5,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [454] [4316] :=
    ⟨Fin 6, «FinitePoly [[2,3,4,5,5,0],[1,4,4,5,5,0],[2,4,4,5,5,0],[1,3,3,5,5,0],[2,4,4,5,5,0],[2,3,4,5,5,0]]», by decideFin!⟩
