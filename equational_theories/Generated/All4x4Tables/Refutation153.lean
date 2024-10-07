
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[3,2,1,0],[0,1,2,3],[1,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[3,2,1,0],[0,1,2,3],[1,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[3,2,1,0],[0,1,2,3],[1,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[3,2,1,0],[0,1,2,3],[1,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1673, 2558, 2737, 4477, 4482] [307, 359, 477, 504, 511, 513, 680, 707, 883, 917, 1086, 1113, 1122, 1289, 1325, 1526, 1528, 1635, 2447, 2459, 3261, 3306, 4283, 4290, 4320, 4396, 4398, 4405, 4433, 4435, 4442, 4598, 4635] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[3,2,1,0],[0,1,2,3],[1,3,3,2]]», by decideFin!⟩
