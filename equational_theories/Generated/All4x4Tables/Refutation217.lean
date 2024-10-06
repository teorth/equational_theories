
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [473, 3271] [513, 3278, 3456, 3659, 4320, 4590] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]», by decideFin!⟩
