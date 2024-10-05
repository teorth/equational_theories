
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2420, 3115] [1657, 1721, 3065, 3253, 3458, 3461, 3519, 3664, 3674, 3677, 3749, 4070, 4131, 4269, 4272] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,3],[2,3,3,2],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
