
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,2,1],[0,3,2,1],[2,1,0,3],[2,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,2,1],[0,3,2,1],[2,1,0,3],[2,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,2,1],[0,3,2,1],[2,1,0,3],[2,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,2,1],[0,3,2,1],[2,1,0,3],[2,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1340, 1488] [1241, 1285, 1515, 1654, 1684, 2053, 2097, 4083, 4090, 4158, 4165, 4622, 4635] :=
    ⟨Fin 4, «FinitePoly [[0,3,2,1],[0,3,2,1],[2,1,0,3],[2,1,0,3]]», by decideFin!⟩
