
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,5,3,4],[1,4,3,5,0,2],[5,4,0,1,3,2],[1,2,0,5,3,4],[5,4,0,1,3,2],[1,4,3,5,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,5,3,4],[1,4,3,5,0,2],[5,4,0,1,3,2],[1,2,0,5,3,4],[5,4,0,1,3,2],[1,4,3,5,0,2]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,0,5,3,4],[1,4,3,5,0,2],[5,4,0,1,3,2],[1,2,0,5,3,4],[5,4,0,1,3,2],[1,4,3,5,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,5,3,4],[1,4,3,5,0,2],[5,4,0,1,3,2],[1,2,0,5,3,4],[5,4,0,1,3,2],[1,4,3,5,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [690] [1426, 3862] :=
    ⟨Fin 6, «FinitePoly [[1,2,0,5,3,4],[1,4,3,5,0,2],[5,4,0,1,3,2],[1,2,0,5,3,4],[5,4,0,1,3,2],[1,4,3,5,0,2]]», by decideFin!⟩
