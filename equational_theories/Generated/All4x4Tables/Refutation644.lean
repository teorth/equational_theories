
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,2,2,4],[0,4,3,3,4],[0,4,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,2,2,4],[0,4,3,3,4],[0,4,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,1,2,2,4],[0,4,3,3,4],[0,4,4,3,4],[4,1,2,4,4],[0,1,2,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,2,2,4],[0,4,3,3,4],[0,4,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3180] [2290, 2300, 2303, 2327, 2530, 2659, 3255, 3261, 3467, 4131, 4269] :=
    ⟨Fin 5, «FinitePoly [[2,1,2,2,4],[0,4,3,3,4],[0,4,4,3,4],[4,1,2,4,4],[0,1,2,3,4]]», by decideFin!⟩
