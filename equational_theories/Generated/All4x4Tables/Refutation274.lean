
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2588, 2812] [211, 307, 2238, 2662, 3058, 3152, 3458, 3464, 3509, 3522, 3659, 4090, 4118, 4165, 4622] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,1],[2,2,3,3],[2,2,3,3],[0,1,2,3]]», by decideFin!⟩
