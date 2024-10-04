
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2351, 2385, 2406] [211, 221, 1629, 2240, 2246, 2263, 2327, 2446, 2466, 2496, 2506, 2530, 2533, 2543, 2644, 3050, 3253, 3456, 3659, 4090, 4118, 4131, 4165, 4269, 4272, 4622] :=
    ⟨Fin 4, «FinitePoly [[2,3,3,3],[3,3,2,3],[2,3,1,3],[0,1,2,3]]», by decideFin!⟩
