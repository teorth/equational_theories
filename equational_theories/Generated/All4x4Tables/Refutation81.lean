
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,3],[2,3,2,2],[1,1,2,3],[0,0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,3],[2,3,2,2],[1,1,2,3],[0,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,3],[2,3,2,2],[1,1,2,3],[0,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,3],[2,3,2,2],[1,1,2,3],[0,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2259, 2277, 2462, 2469] [151, 1629, 2281, 2449, 2466, 2644, 3050, 3253, 3456, 3659, 4065, 4269, 4270, 4314, 4320, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,3],[2,3,2,2],[1,1,2,3],[0,0,2,0]]», by decideFin!⟩
