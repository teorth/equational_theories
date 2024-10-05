
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1437, 1447, 2273] [1451, 1454, 4070, 4073, 4121, 4128, 4360, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,3,2,3],[2,3,2,1],[0,1,2,1]]», by decideFin!⟩
