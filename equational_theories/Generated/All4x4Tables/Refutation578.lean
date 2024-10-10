
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,2,1,1,2],[3,3,5,5,5,3],[3,3,5,5,5,3],[0,4,0,0,4,4],[2,1,2,1,1,2],[0,4,0,0,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,2,1,1,2],[3,3,5,5,5,3],[3,3,5,5,5,3],[0,4,0,0,4,4],[2,1,2,1,1,2],[0,4,0,0,4,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,1,2,1,1,2],[3,3,5,5,5,3],[3,3,5,5,5,3],[0,4,0,0,4,4],[2,1,2,1,1,2],[0,4,0,0,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,2,1,1,2],[3,3,5,5,5,3],[3,3,5,5,5,3],[0,4,0,0,4,4],[2,1,2,1,1,2],[0,4,0,0,4,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2074] [3255, 3261, 3309, 3319, 4269, 4284] :=
    ⟨Fin 6, «FinitePoly [[2,1,2,1,1,2],[3,3,5,5,5,3],[3,3,5,5,5,3],[0,4,0,0,4,4],[2,1,2,1,1,2],[0,4,0,0,4,4]]», by decideFin!⟩
