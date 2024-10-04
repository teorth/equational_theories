
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,1,1],[3,0,3,0],[3,0,3,0],[2,2,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,1,1],[3,0,3,0],[3,0,3,0],[2,2,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,1,1],[3,0,3,0],[3,0,3,0],[2,2,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,1,1],[3,0,3,0],[3,0,3,0],[2,2,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1447, 1461] [1434, 1454, 1473, 4284, 4287] :=
    ⟨Fin 4, «FinitePoly [[2,2,1,1],[3,0,3,0],[3,0,3,0],[2,2,1,1]]», by decideFin!⟩
