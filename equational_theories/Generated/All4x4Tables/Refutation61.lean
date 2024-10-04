
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,1,3,2],[1,2,1,3],[1,3,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,1],[3,1,3,2],[1,2,1,3],[1,3,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,1],[3,1,3,2],[1,2,1,3],[1,3,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,1],[3,1,3,2],[1,2,1,3],[1,3,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3865] [3659, 3870, 4065, 4270, 4598, 4673] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,1],[3,1,3,2],[1,2,1,3],[1,3,1,1]]», by decideFin!⟩
