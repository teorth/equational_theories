
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,3],[1,0,1,1],[0,1,0,3],[3,1,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,3],[1,0,1,1],[0,1,0,3],[3,1,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,0,3],[1,0,1,1],[0,1,0,3],[3,1,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,3],[1,0,1,1],[0,1,0,3],[3,1,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3350, 4229] [40, 3259, 3261, 3269, 3271, 3278, 3472, 3659, 3878, 4068, 4098] :=
    ⟨Fin 4, «FinitePoly [[0,1,0,3],[1,0,1,1],[0,1,0,3],[3,1,3,2]]», by decideFin!⟩
