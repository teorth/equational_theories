
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,5,0,1,4],[2,5,3,4,1,0],[2,5,3,4,1,0],[1,5,3,0,2,4],[2,3,5,0,1,4],[1,5,3,0,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,5,0,1,4],[2,5,3,4,1,0],[2,5,3,4,1,0],[1,5,3,0,2,4],[2,3,5,0,1,4],[1,5,3,0,2,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[2,3,5,0,1,4],[2,5,3,4,1,0],[2,5,3,4,1,0],[1,5,3,0,2,4],[2,3,5,0,1,4],[1,5,3,0,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,5,0,1,4],[2,5,3,4,1,0],[2,5,3,4,1,0],[1,5,3,0,2,4],[2,3,5,0,1,4],[1,5,3,0,2,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [860, 1586] [47, 614, 819, 835, 842, 1428, 1431, 1434, 1441, 1444, 1454, 3862, 4067, 4073, 4118, 4121, 4128, 4131, 4269, 4284, 4599, 4631] :=
    ⟨Fin 6, «FinitePoly [[2,3,5,0,1,4],[2,5,3,4,1,0],[2,5,3,4,1,0],[1,5,3,0,2,4],[2,3,5,0,1,4],[1,5,3,0,2,4]]», by decideFin!⟩
