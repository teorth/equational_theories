
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [387] [3306, 3308, 3353, 3355, 3511, 3518, 3549, 3556, 3722, 3724, 3749, 3917, 3924, 3955, 3962, 4127, 4131, 4154, 4158] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,1,0,1],[1,0,2,0],[3,1,0,1]]», by decideFin!⟩
