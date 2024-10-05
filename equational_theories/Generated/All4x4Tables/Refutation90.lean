
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2456, 2530, 2770, 4155] [2238, 2466, 2646, 2652, 2662, 2672, 2706, 3253, 3659, 4090, 4128, 4131, 4314, 4320, 4631] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,1],[3,1,2,3],[0,1,3,1],[0,1,2,1]]», by decideFin!⟩
